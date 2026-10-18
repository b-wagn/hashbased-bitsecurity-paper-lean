import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Fresh request sampling preserves the signer-counted cost: direct hashes cost one,
and each reference signing attempt costs two. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

open Generic.DeterministicSigning

attribute [local irreducible] Generic.Seeded.tableSign Generic.Seeded.sampleRandomizerOutputs

noncomputable def weightedCostHash (weight : Nat) :
    QueryImpl HashSpec (StateT Generic.Seeded.CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  return (result.1, result.2, state.2 + weight)

theorem run_weightedCostQuery (weight : Nat) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (cost : Nat) :
    ((Generic.Seeded.worldHandler (weightedCostHash weight)) input).run (cache, cost) =
      (fun result => (result.1, result.2, cost + weight * Generic.Seeded.queryCost input)) <$>
        (Generic.romImpl input).run cache := by
  cases input with
  | inl input =>
      simp only [Generic.Seeded.queryCost]
      rfl
  | inr input =>
      change (do
        let result ← (randomOracle input).run cache
        pure (result.1, result.2, cost + weight)) = _
      rw [bind_pure_comp]
      simp only [Generic.Seeded.queryCost, if_true, Nat.mul_one]
      rfl

theorem run_weightedCostWorld {α : Type} (weight : Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (Generic.Seeded.worldHandler (weightedCostHash weight)) computation).run (cache, cost) =
      (fun result => (result.1.1, result.2, cost + weight * result.1.2)) <$>
        (simulateQ Generic.romImpl (Generic.countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value =>
      simp only [simulateQ_pure, Generic.countHashQueries_pure, StateT.run_pure, map_pure,
        Nat.mul_zero, Nat.add_zero]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        Generic.countHashQueries_query_bind, simulateQ_pure, StateT.run_pure, map_bind,
        run_weightedCostQuery, bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, Generic.Seeded.queryCost, Nat.mul_add, Nat.add_assoc]
      rfl

theorem chargedSigning_eq_weightedCostWorld (weight : Nat)
    (computation : OracleComp OracleWorld (Option Generic.Signature)) :
    chargedSigning weight computation =
      simulateQ (Generic.Seeded.worldHandler (weightedCostHash weight)) computation := by
  funext state
  exact (run_weightedCostWorld weight computation state.1 state.2).symm

noncomputable local instance : SampleableType Generic.Seeded.TrialTape := Generic.Seeded.trialTapeSampleableType
noncomputable local instance : SampleableType Generic.Seeded.RequestTapes := Generic.Seeded.requestTapesSampleableType

theorem tableRun_separate_lift_requests {α Tape State : Type}
    (base handler : QueryImpl OracleWorld (StateT State ProbComp))
    (kernel : Generic.SignRequest → Tape → OracleComp HashSpec (Option Generic.Signature))
    (signing : Generic.SignRequest → OracleComp HashSpec (Option Generic.Signature))
    (tapes : Generic.SignRequest → Tape)
    (hsign : ∀ request, kernel request (tapes request) = signing request)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    Generic.DeterministicSigning.tableRun base (fun request tape => simulateQ handler
      (liftM (kernel request tape) : OracleComp OracleWorld (Option Generic.Signature))) tapes computation =
      simulateQ (base + fun request => simulateQ handler
        (liftM (signing request) : OracleComp OracleWorld (Option Generic.Signature))) computation := by
  unfold Generic.DeterministicSigning.tableRun
  apply congrArg (fun implementation => simulateQ implementation computation)
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      exact congrArg (fun signing : OracleComp HashSpec (Option Generic.Signature) =>
        simulateQ handler (liftM signing : OracleComp OracleWorld (Option Generic.Signature))) (hsign request)

theorem tableRun_separate_requests {α State : Type}
    (base : QueryImpl OracleWorld (StateT State ProbComp))
    (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : Generic.SecretKey) (tapes : Generic.Seeded.RequestTapes)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    Generic.DeterministicSigning.tableRun base (Generic.Seeded.requestKernel hash secretKey) tapes computation =
      simulateQ (base + fun (request : Generic.SignRequest) =>
        simulateQ (Generic.Seeded.worldHandler hash)
          (liftM (Generic.Seeded.tableSign (Function.uncurry tapes) secretKey request.epoch request.message :
            OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld _)) computation := by
  exact tableRun_separate_lift_requests base (Generic.Seeded.worldHandler hash)
    (fun (request : Generic.SignRequest) tape => Generic.Seeded.tableSign (fun position => tape position.2)
      secretKey request.epoch request.message)
    (fun (request : Generic.SignRequest) => Generic.Seeded.tableSign (Function.uncurry tapes)
      secretKey request.epoch request.message) tapes
    (fun request => (Generic.Seeded.tableSign_own (m := OracleComp HashSpec)
      (Function.uncurry tapes) secretKey request).symm) computation

/-- The base oracle and the signer can use different state handlers, including different
cost rates, when replacing a table of randomizers by fresh sampling. -/
theorem evalDist_tableRequests_separateHandlers {α State : Type} {used : Set Generic.SignRequest}
    (base : QueryImpl OracleWorld (StateT State ProbComp))
    (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hfresh : Generic.DeterministicSigning.FreshRequests used computation) (state : State) :
    𝒟[do
      let randomizers ← Generic.Seeded.sampleRandomizerOutputs
      (simulateQ (base + fun (request : Generic.SignRequest) =>
        simulateQ (Generic.Seeded.worldHandler hash)
          (liftM (Generic.Seeded.tableSign randomizers secretKey request.epoch request.message :
            OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld _))
        computation).run state] =
      𝒟[(simulateQ (base + fun (request : Generic.SignRequest) =>
        simulateQ (Generic.Seeded.worldHandler hash)
          (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message))
        computation).run state] := by
  conv_lhs => rw [evalDist_bind, ← Generic.Seeded.evalDist_uncurry_tapes, ← evalDist_bind, bind_map_left]
  simp_rw [← tableRun_separate_requests base hash secretKey]
  exact (hfresh.evalDist_tableRun base (Generic.Seeded.requestKernel hash secretKey) state).trans
    (Generic.Seeded.evalDist_freshRun_of_kernel base (Generic.Seeded.requestKernel hash secretKey)
      (fun request => simulateQ (Generic.Seeded.worldHandler hash)
        (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message))
      (fun request state => Generic.Seeded.evalDist_tableSign hash secretKey request.epoch request.message state)
      computation state)

noncomputable def referencePhaseCostImpl (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT Generic.Seeded.CostState ProbComp) :=
  Generic.Seeded.worldHandler Generic.Seeded.costHash + fun (request : Generic.SignRequest) =>
    chargedSigning 2 (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message)

theorem evalDist_tablePhaseCost_eq_reference {α : Type} {used : Set Generic.SignRequest}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hfresh : Generic.DeterministicSigning.FreshRequests used computation) (state : Generic.Seeded.CostState) :
    𝒟[do
      let randomizers ← Generic.Seeded.sampleRandomizerOutputs
      (simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state] =
      𝒟[(simulateQ (referencePhaseCostImpl secretKey) computation).run state] := by
  simp only [tablePhaseCostImpl, referencePhaseCostImpl, chargedSigning_eq_weightedCostWorld]
  exact evalDist_tableRequests_separateHandlers (Generic.Seeded.worldHandler Generic.Seeded.costHash) (weightedCostHash 2)
    secretKey computation hfresh state

theorem referencePhaseCost_le_of_table {α : Type} {used : Set Generic.SignRequest}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hfresh : Generic.DeterministicSigning.FreshRequests used computation) (state : Generic.Seeded.CostState) (q : Nat)
    (hbound : ∀ randomizers, ∀ result ∈ support
      ((simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state),
        result.2.2 ≤ q)
    (result : α × Generic.Seeded.CostState)
    (hresult : result ∈ support
      ((simulateQ (referencePhaseCostImpl secretKey) computation).run state)) :
    result.2.2 ≤ q := by
  rw [← mem_support_iff_of_evalDist_eq
    (evalDist_tablePhaseCost_eq_reference secretKey computation hfresh state),
    mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact hbound randomizers result hresult

/-- info: 'XmssSecurity.TargetSum.Seeded.evalDist_tablePhaseCost_eq_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_tablePhaseCost_eq_reference

/-- info: 'XmssSecurity.TargetSum.Seeded.referencePhaseCost_le_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms referencePhaseCost_le_of_table

end XmssSecurity.TargetSum.Seeded

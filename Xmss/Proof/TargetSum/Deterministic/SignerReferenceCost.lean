import Xmss.Proof.TargetSum.Deterministic.SignerPhaseCost
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Fresh request sampling preserves the signer-counted cost: direct hashes cost one,
and each reference signing attempt costs two. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Seeded

open DeterministicSigning

attribute [local irreducible] Seeded.tableSign Seeded.sampleRandomizerOutputs

noncomputable def weightedCostHash (weight : Nat) :
    QueryImpl HashSpec (StateT Seeded.CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  return (result.1, result.2, state.2 + weight)

theorem run_weightedCostQuery (weight : Nat) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (cost : Nat) :
    ((Seeded.worldHandler (weightedCostHash weight)) input).run (cache, cost) =
      (fun result => (result.1, result.2, cost + weight * Seeded.queryCost input)) <$>
        (romImpl input).run cache := by
  cases input with
  | inl input =>
      simp only [Seeded.queryCost]
      rfl
  | inr input =>
      change (do
        let result ← (randomOracle input).run cache
        pure (result.1, result.2, cost + weight)) = _
      rw [bind_pure_comp]
      simp only [Seeded.queryCost, if_true, Nat.mul_one]
      rfl

theorem run_weightedCostWorld {α : Type} (weight : Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (Seeded.worldHandler (weightedCostHash weight)) computation).run (cache, cost) =
      (fun result => (result.1.1, result.2, cost + weight * result.1.2)) <$>
        (simulateQ romImpl (countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value =>
      simp only [simulateQ_pure, countHashQueries_pure, StateT.run_pure, map_pure,
        Nat.mul_zero, Nat.add_zero]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        countHashQueries_query_bind, simulateQ_pure, StateT.run_pure, map_bind,
        run_weightedCostQuery, bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, Seeded.queryCost, Nat.mul_add, Nat.add_assoc]
      rfl

theorem chargedSigning_eq_weightedCostWorld (weight : Nat)
    (computation : OracleComp OracleWorld (Option Generic.Signature)) :
    chargedSigning weight computation =
      simulateQ (Seeded.worldHandler (weightedCostHash weight)) computation := by
  funext state
  exact (run_weightedCostWorld weight computation state.1 state.2).symm

noncomputable local instance : SampleableType Seeded.TrialTape := Seeded.trialTapeSampleableType
noncomputable local instance : SampleableType Seeded.RequestTapes := Seeded.requestTapesSampleableType

theorem tableRun_separate_lift_requests {α Tape State : Type}
    (base handler : QueryImpl OracleWorld (StateT State ProbComp))
    (kernel : SignRequest → Tape → OracleComp HashSpec (Option Generic.Signature))
    (signing : SignRequest → OracleComp HashSpec (Option Generic.Signature))
    (tapes : SignRequest → Tape)
    (hsign : ∀ request, kernel request (tapes request) = signing request)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeterministicSigning.tableRun base (fun request tape => simulateQ handler
      (liftM (kernel request tape) : OracleComp OracleWorld (Option Generic.Signature))) tapes computation =
      simulateQ (base + fun request => simulateQ handler
        (liftM (signing request) : OracleComp OracleWorld (Option Generic.Signature))) computation := by
  unfold DeterministicSigning.tableRun
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
    (secretKey : Generic.SecretKey) (tapes : Seeded.RequestTapes)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    DeterministicSigning.tableRun base (Seeded.requestKernel hash secretKey) tapes computation =
      simulateQ (base + fun (request : SignRequest) =>
        simulateQ (Seeded.worldHandler hash)
          (liftM (Seeded.tableSign (Function.uncurry tapes) secretKey request.epoch request.message :
            OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld _)) computation := by
  exact tableRun_separate_lift_requests base (Seeded.worldHandler hash)
    (fun (request : SignRequest) tape => Seeded.tableSign (fun position => tape position.2)
      secretKey request.epoch request.message)
    (fun (request : SignRequest) => Seeded.tableSign (Function.uncurry tapes)
      secretKey request.epoch request.message) tapes
    (fun request => (Seeded.tableSign_own (m := OracleComp HashSpec)
      (Function.uncurry tapes) secretKey request).symm) computation

/-- The base oracle and the signer can use different state handlers, including different
cost rates, when replacing a table of randomizers by fresh sampling. -/
theorem evalDist_tableRequests_separateHandlers {α State : Type} {used : Set SignRequest}
    (base : QueryImpl OracleWorld (StateT State ProbComp))
    (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hfresh : DeterministicSigning.FreshRequests used computation) (state : State) :
    𝒟[do
      let randomizers ← Seeded.sampleRandomizerOutputs
      (simulateQ (base + fun (request : SignRequest) =>
        simulateQ (Seeded.worldHandler hash)
          (liftM (Seeded.tableSign randomizers secretKey request.epoch request.message :
            OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld _))
        computation).run state] =
      𝒟[(simulateQ (base + fun (request : SignRequest) =>
        simulateQ (Seeded.worldHandler hash)
          (Signing.precomputedCappedSign secretKey request.epoch request.message))
        computation).run state] := by
  conv_lhs => rw [evalDist_bind, ← Seeded.evalDist_uncurry_tapes, ← evalDist_bind, bind_map_left]
  simp_rw [← tableRun_separate_requests base hash secretKey]
  exact (hfresh.evalDist_tableRun base (Seeded.requestKernel hash secretKey) state).trans
    (Seeded.evalDist_freshRun_of_kernel base (Seeded.requestKernel hash secretKey)
      (fun request => simulateQ (Seeded.worldHandler hash)
        (Signing.precomputedCappedSign secretKey request.epoch request.message))
      (fun request state => Seeded.evalDist_tableSign hash secretKey request.epoch request.message state)
      computation state)

noncomputable def referencePhaseCostImpl (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT Seeded.CostState ProbComp) :=
  Seeded.worldHandler Seeded.costHash + fun (request : SignRequest) =>
    chargedSigning 2 (Signing.precomputedCappedSign secretKey request.epoch request.message)

theorem evalDist_tablePhaseCost_eq_reference {α : Type} {used : Set SignRequest}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hfresh : DeterministicSigning.FreshRequests used computation) (state : Seeded.CostState) :
    𝒟[do
      let randomizers ← Seeded.sampleRandomizerOutputs
      (simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state] =
      𝒟[(simulateQ (referencePhaseCostImpl secretKey) computation).run state] := by
  simp only [tablePhaseCostImpl, referencePhaseCostImpl, chargedSigning_eq_weightedCostWorld]
  exact evalDist_tableRequests_separateHandlers (Seeded.worldHandler Seeded.costHash) (weightedCostHash 2)
    secretKey computation hfresh state

theorem referencePhaseCost_le_of_table {α : Type} {used : Set SignRequest}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hfresh : DeterministicSigning.FreshRequests used computation) (state : Seeded.CostState) (q : Nat)
    (hbound : ∀ randomizers, ∀ result ∈ support
      ((simulateQ (tablePhaseCostImpl randomizers secretKey) computation).run state),
        result.2.2 ≤ q)
    (result : α × Seeded.CostState)
    (hresult : result ∈ support
      ((simulateQ (referencePhaseCostImpl secretKey) computation).run state)) :
    result.2.2 ≤ q := by
  rw [← mem_support_iff_of_evalDist_eq
    (evalDist_tablePhaseCost_eq_reference secretKey computation hfresh state),
    mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact hbound randomizers result hresult

/-- info: 'Xmss.TargetSum.Seeded.evalDist_tablePhaseCost_eq_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_tablePhaseCost_eq_reference

/-- info: 'Xmss.TargetSum.Seeded.referencePhaseCost_le_of_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms referencePhaseCost_le_of_table

end Xmss.TargetSum.Seeded

import XmssSecurity.Proof.TargetSum.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.Generic.Deterministic.ReferenceSource
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Keep the direct and signer hash counts separate while preserving the complete
reference execution, including its final cache. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

structure PhaseCounts where
  cache : QueryCache HashSpec
  direct : Nat
  signing : Nat

def PhaseCounts.weighted (weight : Nat) (state : PhaseCounts) : Generic.Seeded.CostState :=
  (state.cache, state.direct + weight * state.signing)

noncomputable def phaseCountsImpl
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature)) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT PhaseCounts ProbComp) := fun input state =>
  match input with
  | .inl worldInput =>
      (fun result => (result.1, ⟨result.2, state.direct + Generic.Seeded.queryCost worldInput, state.signing⟩)) <$>
        (Generic.romImpl worldInput).run state.cache
  | .inr request =>
      (fun result => (result.1.1, ⟨result.2, state.direct, state.signing + result.1.2⟩)) <$>
        (simulateQ Generic.romImpl (Generic.countHashQueries (signing request))).run state.cache

noncomputable def weightedPhaseCostImpl (weight : Nat)
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature)) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT Generic.Seeded.CostState ProbComp) :=
  Generic.Seeded.worldHandler Generic.Seeded.costHash + fun request => chargedSigning weight (signing request)

theorem phaseCountsImpl_weighted_projection
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature)) (weight : Nat)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (phaseCountsImpl signing input).run state =
        (weightedPhaseCostImpl weight signing input).run (state.weighted weight) := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1,
        (result.2, (state.direct + Generic.Seeded.queryCost input) + weight * state.signing))) <$>
          (Generic.romImpl input).run state.cache =
        ((Generic.Seeded.worldHandler Generic.Seeded.costHash) input).run (state.cache, state.direct + weight * state.signing)
      rw [Generic.Seeded.run_costQuery]
      congr 1
      funext result
      exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1.1,
        (result.2, state.direct + weight * (state.signing + result.1.2)))) <$>
          (simulateQ Generic.romImpl (Generic.countHashQueries (signing request))).run state.cache =
        (fun result => (result.1.1,
          (result.2, (state.direct + weight * state.signing) + weight * result.1.2))) <$>
            (simulateQ Generic.romImpl (Generic.countHashQueries (signing request))).run state.cache
      simp only [Nat.mul_add, Nat.add_assoc]

theorem phaseCounts_weighted_projection {α : Type}
    (signing : Generic.SignRequest → OracleComp OracleWorld (Option Generic.Signature)) (weight : Nat)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (simulateQ (phaseCountsImpl signing) computation).run state =
        (simulateQ (weightedPhaseCostImpl weight signing) computation).run
          (state.weighted weight) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (phaseCountsImpl_weighted_projection signing weight) computation state

noncomputable def referencePhaseCountsImpl (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT PhaseCounts ProbComp) :=
  phaseCountsImpl (fun request =>
    Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message)

theorem referencePhaseCounts_cost_projection {α : Type}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted 2) <$>
      (simulateQ (referencePhaseCountsImpl secretKey) computation).run state =
        (simulateQ (referencePhaseCostImpl secretKey) computation).run (state.weighted 2) :=
  phaseCounts_weighted_projection _ 2 computation state

/-- info: 'XmssSecurity.TargetSum.Seeded.phaseCounts_weighted_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseCounts_weighted_projection

end XmssSecurity.TargetSum.Seeded

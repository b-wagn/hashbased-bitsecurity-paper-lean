import Xmss.Proof.TargetSum.Deterministic.SignerReferenceCost
import Xmss.Proof.Generic.Deterministic.ReferenceSource
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Keep the direct and signer hash counts separate while preserving the complete
reference execution, including its final cache. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Seeded

structure PhaseCounts where
  cache : QueryCache HashSpec
  direct : Nat
  signing : Nat

def PhaseCounts.weighted (weight : Nat) (state : PhaseCounts) : Seeded.CostState :=
  (state.cache, state.direct + weight * state.signing)

noncomputable def phaseCountsImpl
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT PhaseCounts ProbComp) := fun input state =>
  match input with
  | .inl worldInput =>
      (fun result => (result.1, ⟨result.2, state.direct + Seeded.queryCost worldInput, state.signing⟩)) <$>
        (romImpl worldInput).run state.cache
  | .inr request =>
      (fun result => (result.1.1, ⟨result.2, state.direct, state.signing + result.1.2⟩)) <$>
        (simulateQ romImpl (countHashQueries (signing request))).run state.cache

noncomputable def weightedPhaseCostImpl (weight : Nat)
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT Seeded.CostState ProbComp) :=
  Seeded.worldHandler Seeded.costHash + fun request => chargedSigning weight (signing request)

theorem phaseCountsImpl_weighted_projection
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature)) (weight : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (phaseCountsImpl signing input).run state =
        (weightedPhaseCostImpl weight signing input).run (state.weighted weight) := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1,
        (result.2, (state.direct + Seeded.queryCost input) + weight * state.signing))) <$>
          (romImpl input).run state.cache =
        ((Seeded.worldHandler Seeded.costHash) input).run (state.cache, state.direct + weight * state.signing)
      rw [Seeded.run_costQuery]
      congr 1
      funext result
      exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
  | inr request =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1.1,
        (result.2, state.direct + weight * (state.signing + result.1.2)))) <$>
          (simulateQ romImpl (countHashQueries (signing request))).run state.cache =
        (fun result => (result.1.1,
          (result.2, (state.direct + weight * state.signing) + weight * result.1.2))) <$>
            (simulateQ romImpl (countHashQueries (signing request))).run state.cache
      simp only [Nat.mul_add, Nat.add_assoc]

theorem phaseCounts_weighted_projection {α : Type}
    (signing : SignRequest → OracleComp OracleWorld (Option Generic.Signature)) (weight : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (simulateQ (phaseCountsImpl signing) computation).run state =
        (simulateQ (weightedPhaseCostImpl weight signing) computation).run
          (state.weighted weight) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (phaseCountsImpl_weighted_projection signing weight) computation state

noncomputable def referencePhaseCountsImpl (secretKey : Generic.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT PhaseCounts ProbComp) :=
  phaseCountsImpl (fun request =>
    Signing.precomputedCappedSign secretKey request.epoch request.message)

theorem referencePhaseCounts_cost_projection {α : Type}
    (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted 2) <$>
      (simulateQ (referencePhaseCountsImpl secretKey) computation).run state =
        (simulateQ (referencePhaseCostImpl secretKey) computation).run (state.weighted 2) :=
  phaseCounts_weighted_projection _ 2 computation state

/-- info: 'Xmss.TargetSum.Seeded.phaseCounts_weighted_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseCounts_weighted_projection

end Xmss.TargetSum.Seeded

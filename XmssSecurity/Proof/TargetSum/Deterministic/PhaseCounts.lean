import XmssSecurity.Proof.TargetSum.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.TargetSum.Deterministic.ReferenceSource
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! Keep the direct and signer hash counts separate while preserving the complete
reference execution, including its final cache. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

structure PhaseCounts where
  cache : QueryCache HashSpec
  direct : Nat
  signing : Nat

def PhaseCounts.weighted (weight : Nat) (state : PhaseCounts) : CostState :=
  (state.cache, state.direct + weight * state.signing)

noncomputable def phaseCountsImpl
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT PhaseCounts ProbComp) := fun input state =>
  match input with
  | .inl worldInput =>
      (fun result => (result.1, ⟨result.2, state.direct + queryCost worldInput, state.signing⟩)) <$>
        (romImpl worldInput).run state.cache
  | .inr request =>
      (fun result => (result.1.1, ⟨result.2, state.direct, state.signing + result.1.2⟩)) <$>
        (simulateQ romImpl (countHashQueries (signing request))).run state.cache

noncomputable def weightedPhaseCostImpl (weight : Nat)
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CostState ProbComp) :=
  worldHandler costHash + fun request => chargedSigning weight (signing request)

theorem phaseCountsImpl_weighted_projection
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) (weight : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (phaseCountsImpl signing input).run state =
        (weightedPhaseCostImpl weight signing input).run (state.weighted weight) := by
  cases input with
  | inl input =>
      simp only [phaseCountsImpl, StateT.run, Functor.map_map]
      change (fun result => (result.1,
        (result.2, (state.direct + queryCost input) + weight * state.signing))) <$>
          (romImpl input).run state.cache =
        ((worldHandler costHash) input).run (state.cache, state.direct + weight * state.signing)
      rw [run_costQuery]
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
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) (weight : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted weight) <$>
      (simulateQ (phaseCountsImpl signing) computation).run state =
        (simulateQ (weightedPhaseCostImpl weight signing) computation).run
          (state.weighted weight) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (phaseCountsImpl_weighted_projection signing weight) computation state

theorem weightedPhaseCostImpl_one
    (signing : SignRequest → OracleComp OracleWorld (Option Signature)) :
    weightedPhaseCostImpl 1 signing =
      worldHandler costHash + fun request => simulateQ (worldHandler costHash) (signing request) := by
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      funext state
      exact chargedSigning_one (signing request) state

theorem phaseCounts_fullHashCount_projection {α : Type}
    (signing : SignRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    (fun result => (result.1, result.2.cache, result.2.direct + result.2.signing)) <$>
      (simulateQ (phaseCountsImpl signing) computation).run state =
        (simulateQ (worldHandler costHash) (runWorldSigning signing computation)).run
          (state.cache, state.direct + state.signing) := by
  have h := phaseCounts_weighted_projection signing 1 computation state
  rw [weightedPhaseCostImpl_one, ← simulateQ_runWorldSigning] at h
  have hproject : Prod.map (id : α → α) (PhaseCounts.weighted 1) =
      fun result => (result.1, result.2.cache, result.2.direct + result.2.signing) := by
    funext result
    simp only [Prod.map, PhaseCounts.weighted, Nat.one_mul, id_eq]
  rw [hproject] at h
  simpa only [PhaseCounts.weighted, Nat.one_mul] using h

theorem phaseCounts_cache_projection {α : Type}
    (signing : SignRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    (fun result => (result.1, result.2.cache)) <$>
      (simulateQ (phaseCountsImpl signing) computation).run state =
        (simulateQ romImpl (runWorldSigning signing computation)).run state.cache := by
  have h := congrArg (fun execution => (fun result => (result.1, result.2.1)) <$> execution)
    (phaseCounts_fullHashCount_projection signing computation state)
  rw [run_costWorld] at h
  simpa only [Functor.map_map, countHashQueries_run_forget] using h

noncomputable def referencePhaseCountsImpl (secretKey : XmssSecurity.TargetSum.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT PhaseCounts ProbComp) :=
  phaseCountsImpl (fun request =>
    Concrete.precomputedCappedSign secretKey request.epoch request.message)

theorem referencePhaseCounts_cost_projection {α : Type}
    (secretKey : XmssSecurity.TargetSum.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : PhaseCounts) :
    Prod.map id (PhaseCounts.weighted 2) <$>
      (simulateQ (referencePhaseCountsImpl secretKey) computation).run state =
        (simulateQ (referencePhaseCostImpl secretKey) computation).run (state.weighted 2) :=
  phaseCounts_weighted_projection _ 2 computation state

/-- info: 'XmssSecurity.TargetSum.Seeded.phaseCounts_weighted_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseCounts_weighted_projection

/-- info: 'XmssSecurity.TargetSum.Seeded.phaseCounts_fullHashCount_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phaseCounts_fullHashCount_projection

end XmssSecurity.TargetSum.Seeded

import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe

/-! Transfer accepted source-prefix events to the limited public experiment and its
expected collision bound, using only the source's semantic weighted query budget. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicLimitedAcceptedPrefixProbeExecution (limit : Nat) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedAcceptedPrefixProbeExecution limit key edgeHigh (adversary.main key.publicKey)

theorem sourceAcceptedLimitedPrefix_coupling_afterKeygen
    (adversary : Adversary) (limit : Nat)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (adversary.main left.publicKey) (CountedSourceState.initial left.cache)) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicLimitedAcceptedPrefixProbeExecution limit adversary right.1.1 right.2)).run)
      (fun source target => AcceptedPrefixFirstLaneEvent left source →
        CombinedHit right.1.2 (enforceHazardTrace (limit + 1) target.2)) := by
  have hcoupling := limitedAcceptedPrefixEvent_coupling left right hrel hleftSupport hrightSupport
    limit (adversary.main left.publicKey) hbudget
  have hmapped : RelTriple
      (Prod.map id CountedSourceState.toSource <$>
        ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
          (adversary.main left.publicKey)).run (CountedSourceState.initial left.cache)))
      (id <$> (simulateQ (eagerTraceImpl right.1.2)
        (limitedAcceptedPrefixProbeExecution limit right.1.1 right.2 (adversary.main left.publicKey))).run)
      (fun source target => AcceptedPrefixFirstLaneEvent left source →
        CombinedHit right.1.2 (enforceHazardTrace (limit + 1) target.2)) := by
    apply relTriple_map
    apply relTriple_post_mono (relTriple_with_support hcoupling)
    intro source target hresult hevent
    change CombinedHit right.1.2 (enforceHazardTrace (limit + 1) target.2)
    rw [enforceHazardTrace_eq_self_of_count_le _ _
      (limitedAcceptedPrefixProbe_trace_bound right.1.2 limit right.1.1 right.2
        (adversary.main left.publicKey) target hresult.2.2)]
    exact hresult.1 hevent
  rw [countedSource_source_projection left.publicKey, id_map] at hmapped
  change RelTriple (sourcePrefixExecution adversary left)
    ((simulateQ (eagerTraceImpl right.1.2)
      (limitedAcceptedPrefixProbeExecution limit right.1.1 right.2 (adversary.main left.publicKey))).run) _ at hmapped
  have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
  rw [hpk] at hmapped
  exact hmapped

theorem sourceAcceptedLimitedPrefixProgram_coupling (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicLimitedAcceptedPrefixProbeExecution limit adversary))
      (fun source target => AcceptedPrefixFirstLaneEvent source.1 source.2 →
        CombinedHit target.1.1.2 (enforceHazardTrace (limit + 1) target.2.2)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleftSupport, hrightSupport⟩ := hkeys
  apply relTriple_bind (sourceAcceptedLimitedPrefix_coupling_afterKeygen adversary limit left right hkey
    hleftSupport (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hrightSupport)
    (hbudget left hleftSupport))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem acceptedPrefixFirstLane_probability_le_limited_expected (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * expectedCoupledHazards (limit + 1)
        (publicLimitedAcceptedPrefixProbeExecution limit adversary) := by
  calc
    _ ≤ Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (limit + 1) result.2.2) |
        coupledFirstLaneProgram (publicLimitedAcceptedPrefixProbeExecution limit adversary)] := by
      apply probEvent_le_of_relTriple (sourceAcceptedLimitedPrefixProgram_coupling adversary limit hbudget)
      intro source target hresult hevent
      exact hresult hevent
    _ ≤ _ := coupled_enforcedHit_probability_le_expected (limit + 1)
      (publicLimitedAcceptedPrefixProbeExecution limit adversary)

/-- info: 'XmssSecurity.TargetSum.Deciding.acceptedPrefixFirstLane_probability_le_limited_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedPrefixFirstLane_probability_le_limited_expected

end XmssSecurity.TargetSum.Deciding

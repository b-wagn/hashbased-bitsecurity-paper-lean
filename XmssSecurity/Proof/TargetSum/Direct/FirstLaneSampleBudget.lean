import XmssSecurity.Proof.TargetSum.Direct.CountedSourceEncodingBudget
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCount

/-! Transfer the source encoding budget to observable first-lane traces on the good
branch of the coupling, without identifying the executions after divergence. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem countedSource_encodingBudget_after_trajectory {α : Type}
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ
      (countedSourceImpl (Concrete.materializePrecomputation key.cache key.secretKey))
      computation).run (CountedSourceState.initial key.cache))) :
    CountedSourceEncodingBudget key.secretKey.parameter result.2 := by
  apply countedSource_encodingBudget (Concrete.materializePrecomputation key.cache key.secretKey)
    computation _ _ result hresult
  change cachedEncodingInputCount key.cache key.secretKey.parameter ≤ _
  have hzero := cachedEncodingInputCount_eq_zero_of_no_encodingInputs key.cache key.secretKey.parameter
    (Concrete.keygen_cache_none_encodingInput key.keyResult
      (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey))
  rw [hzero]
  exact zero_le

theorem countedSource_firstLane_encodingSamples_le {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftResult : α × CountedSourceState)
    (rightResult : (α × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hleft : leftResult ∈ support ((simulateQ
      (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache)))
    (hright : rightResult ∈ support ((simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        computation).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run))
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
      rightResult.1.2 rightResult.2) :
    rightResult.2.encodingActions.length ≤
      rightResult.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter +
        leftResult.2.counts.signing := by
  have hsource := countedSource_encodingBudget_after_trajectory left hleftSupport computation leftResult hleft
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter ≤ _ at hsource
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcache := hstate.encodingCount_eq
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter =
    cachedEncodingInputCount rightResult.1.2.causalState.cache left.secretKey.parameter at hcache
  have htrace : leftResult.2.attackerTrace = rightResult.1.2.attackerTrace := hstate.1.2
  rw [hcache, ← hparameter,
    globalFirstLaneExactTraced_encodingCount_eq_trace right.1.2 right.1.1 hrightSupport
      right.2 computation rightResult hright, htrace] at hsource
  exact_mod_cast hsource

noncomputable def observableFirstLaneCharge (parameter : PublicParameter) (state : GlobalHighDirectTracedState)
    (trace : ActionTrace GlobalChainValueIndex) : Nat :=
  hazardCount trace + 2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

theorem countedSource_firstLane_observableCharge_le {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftResult : α × CountedSourceState)
    (rightResult : (α × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hleft : leftResult ∈ support ((simulateQ
      (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache)))
    (hright : rightResult ∈ support ((simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        computation).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run))
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
      rightResult.1.2 rightResult.2)
    (hhazards : hazardCount rightResult.2 ≤ leftResult.2.counts.direct) :
    observableFirstLaneCharge right.1.1.secretKey.parameter rightResult.1.2 rightResult.2 ≤
      leftResult.2.charge := by
  have hsamples := countedSource_firstLane_encodingSamples_le left right hrel hleftSupport hrightSupport
    computation leftResult rightResult hleft hright hstate
  unfold observableFirstLaneCharge CountedSourceState.charge
  omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.countedSource_firstLane_observableCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedSource_firstLane_observableCharge_le

end XmssSecurity.TargetSum.CappedChain

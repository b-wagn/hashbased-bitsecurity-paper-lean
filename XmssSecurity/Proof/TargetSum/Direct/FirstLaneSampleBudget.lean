import XmssSecurity.Proof.TargetSum.Direct.CountedSourceEncodingBudget
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCount
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Transfer the source encoding budget to observable first-lane traces on the good
branch of the coupling, without identifying the executions after divergence. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem countedSource_encodingBudget_after_trajectory {α : Type}
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
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
      (CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey))
  rw [hzero]
  exact zero_le

theorem countedSource_firstLane_encodingSamples_le {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest)) ×
      (CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftResult : α × CountedSourceState)
    (rightResult : (α × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hleft : leftResult ∈ support ((simulateQ
      (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache)))
    (hright : rightResult ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((simulateQ (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        computation).run
          (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState right.1.1)))).run))
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
      rightResult.1.2 rightResult.2) :
    rightResult.2.encodingActions.length ≤
      rightResult.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter +
        leftResult.2.counts.signing := by
  have hsource := countedSource_encodingBudget_after_trajectory left hleftSupport computation leftResult hleft
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter ≤ _ at hsource
  have hparameter := CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcache := SourceFirstLaneExactGoodStateRelation.encodingCount_eq hstate
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter =
    cachedEncodingInputCount rightResult.1.2.causalState.cache left.secretKey.parameter at hcache
  have htrace : leftResult.2.attackerTrace = rightResult.1.2.attackerTrace := hstate.1.2
  rw [hcache, ← hparameter,
    globalFirstLaneExactTraced_encodingCount_eq_trace right.1.2 right.1.1 hrightSupport
      right.2 computation rightResult hright, htrace] at hsource
  exact_mod_cast hsource

noncomputable def observableFirstLaneCharge (parameter : PublicParameter) (state : CappedChain.GlobalHighDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) : Nat :=
  FirstLaneOracleSimulation.hazardCount trace + 2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

end XmssSecurity.TargetSum.CappedChain

import Xmss.Proof.TargetSum.Direct.CountedSourceEncodingBudget
import Xmss.Proof.TargetSum.FirstLaneEncodingCount
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Transfer the source encoding budget to observable first-lane traces on the good
branch of the coupling, without identifying the executions after divergence. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open Seeded FirstLaneOracleSimulation

theorem countedSource_encodingBudget_after_trajectory {α : Type}
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ
      (countedSourceImpl (Keygen.materializePrecomputation key.cache key.secretKey))
      computation).run (CountedSourceState.initial key.cache))) :
    CountedSourceEncodingBudget key.secretKey.parameter result.2 := by
  rw [← Keygen.materializePrecomputation_parameter key.cache key.secretKey]
  apply countedSource_encodingBudget (Keygen.materializePrecomputation key.cache key.secretKey)
    computation _ _ result hresult
  rw [Keygen.materializePrecomputation_parameter]
  change cachedEncodingInputCount key.cache key.secretKey.parameter ≤ _
  have hzero := cachedEncodingInputCount_eq_zero_of_no_encodingInputs key.cache key.secretKey.parameter
    (Keygen.keygen_cache_none_encodingInput key.keyResult
      (CappedExecution.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey))
  rw [hzero]
  exact zero_le

theorem countedSource_firstLane_encodingSamples_le {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftResult : α × CountedSourceState)
    (rightResult : (α × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hleft : leftResult ∈ support ((simulateQ
      (countedSourceImpl (Keygen.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache)))
    (hright : rightResult ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((simulateQ (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl right.1)
        computation).run
          (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState right.1)))).run))
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftResult.2.toSource
      rightResult.1.2 rightResult.2) :
    rightResult.2.encodingActions.length ≤
      rightResult.1.2.attackerTrace.encodingInputCount right.1.secretKey.parameter +
        leftResult.2.counts.signing := by
  have hsource := countedSource_encodingBudget_after_trajectory left hleftSupport computation leftResult hleft
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter ≤ _ at hsource
  have hparameter := CappedExecution.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcache := SourceFirstLaneExactGoodStateRelation.encodingCount_eq hstate
  change cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter =
    cachedEncodingInputCount rightResult.1.2.causalState.cache left.secretKey.parameter at hcache
  have htrace : leftResult.2.attackerTrace = rightResult.1.2.attackerTrace := hstate.1.2
  rw [hcache, ← hparameter,
    globalFirstLaneExactTraced_encodingCount_eq_trace right.2 right.1 hrightSupport
      computation rightResult hright, htrace] at hsource
  exact_mod_cast hsource

noncomputable def observableFirstLaneCharge (parameter : PublicParameter) (state : CappedExecution.GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) : Nat :=
  FirstLaneOracleSimulation.hazardCount trace + 2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

end Xmss.TargetSum.CappedExecution

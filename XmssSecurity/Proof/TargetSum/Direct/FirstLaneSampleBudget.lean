import XmssSecurity.Proof.TargetSum.Direct.CountedSourceEncodingBudget
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCount
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Transfer the source encoding budget to observable first-lane traces on the good
branch of the coupling, without identifying the executions after divergence. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem countedSource_encodingBudget_after_trajectory {α : Type}
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ
      (countedSourceImpl (Generic.Concrete.materializePrecomputation key.cache key.secretKey))
      computation).run (CountedSourceState.initial key.cache))) :
    CountedSourceEncodingBudget key.secretKey.parameter result.2 := by
  apply countedSource_encodingBudget (Generic.Concrete.materializePrecomputation key.cache key.secretKey)
    computation _ _ result hresult
  change Generic.cachedEncodingInputCount key.cache key.secretKey.parameter ≤ _
  have hzero := cachedEncodingInputCount_eq_zero_of_no_encodingInputs key.cache key.secretKey.parameter
    (Generic.Concrete.keygen_cache_none_encodingInput key.keyResult
      (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey))
  rw [hzero]
  exact zero_le

theorem countedSource_firstLane_encodingSamples_le {α : Type}
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (leftResult : α × CountedSourceState)
    (rightResult : (α × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hleft : leftResult ∈ support ((simulateQ
      (countedSourceImpl (Generic.Concrete.materializePrecomputation left.cache left.secretKey))
      computation).run (CountedSourceState.initial left.cache)))
    (hright : rightResult ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((simulateQ (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        computation).run
          (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState right.1.1)))).run))
    (hstate : Generic.CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2.toSource
      rightResult.1.2 rightResult.2) :
    rightResult.2.encodingActions.length ≤
      rightResult.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter +
        leftResult.2.counts.signing := by
  have hsource := countedSource_encodingBudget_after_trajectory left hleftSupport computation leftResult hleft
  change Generic.cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter ≤ _ at hsource
  have hparameter := Generic.CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcache := SourceFirstLaneExactGoodStateRelation.encodingCount_eq hstate
  change Generic.cachedEncodingInputCount leftResult.2.counts.cache left.secretKey.parameter =
    Generic.cachedEncodingInputCount rightResult.1.2.causalState.cache left.secretKey.parameter at hcache
  have htrace : leftResult.2.attackerTrace = rightResult.1.2.attackerTrace := hstate.1.2
  rw [hcache, ← hparameter,
    globalFirstLaneExactTraced_encodingCount_eq_trace right.1.2 right.1.1 hrightSupport
      right.2 computation rightResult hright, htrace] at hsource
  exact_mod_cast hsource

noncomputable def observableFirstLaneCharge (parameter : PublicParameter) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (trace : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) : Nat :=
  Generic.FirstLaneOracleSimulation.hazardCount trace + 2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

end XmssSecurity.TargetSum.CappedChain

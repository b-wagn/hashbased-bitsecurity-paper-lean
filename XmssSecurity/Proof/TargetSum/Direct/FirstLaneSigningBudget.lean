import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSigningSupport
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The observable budget holds through a supported signing step, including the step
that triggers a collision. Its proof uses a supported source witness, not an equality
between the executions after a hit. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem encodingInputCount_eq_of_globalSigning_agree
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn (CappedChain.GlobalSigningComparableHashInput parameter) left right) :
    cachedEncodingInputCount left parameter = cachedEncodingInputCount right parameter := by
  apply cachedEncodingInputCount_eq_of_agree
  intro input hencoding
  obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨⟨message, randomness⟩, hinput⟩ :=
    exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex hleaf
  exact hagrees input ⟨leafIndex, message, randomness, hinput.symm⟩

theorem countedSourceImpl_encodingInputCount_update (secretKey : Generic.SecretKey)
    (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (state : CountedSourceState) (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.encodingInputCount parameter = state.attackerTrace.encodingInputCount parameter +
      (CappedChain.attackerActionFragment input result.1).encodingInputCount parameter := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact CappedChain.AttackerActionTrace.encodingInputCount_append parameter _ _

theorem firstLane_signing_charge_bounds {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest)) ×
      (CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (request : SignRequest) (next : Option Generic.Signature → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedChain.GlobalHighDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= next) leftState)
    (result : (Option Generic.Signature × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inr request)).run rightState)).run)) :
    (leftState.counts.direct + 2 * ((history ++ result.2).encodingActions.length -
      result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  let secretKey := Concrete.materializePrecomputation left.cache left.secretKey
  have hparameter := CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  obtain ⟨monitor, _hobserved, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  obtain ⟨base, hbase, hresultEq⟩ := CappedChain.globalExactTracedLift_eager_support_decompose right.1.2 right.1.1
    (.inr request) (CappedChain.globalFirstLaneSigningImpl right.1.1 request) rightState result hresult
  obtain ⟨source, hsource, hagrees⟩ := exists_countedSource_signing_of_firstLane_support left right hrel
    hleftSupport hrightSupport leftState rightState.causalState hcausal request base hbase
  have hcharge := (hbudget.query_step source hsource).1
  have hsourceEncoding := countedSourceImpl_encodingBudget secretKey (.inr request) leftState
    hencoding source hsource
  have hcacheEq := encodingInputCount_eq_of_globalSigning_agree left.secretKey.parameter
    source.2.counts.cache base.1.2.cache hagrees
  have hfinalCache : result.1.2.causalState.cache = base.1.2.cache := by
    rw [hresultEq, CappedChain.globalExactTracedNextState]
  have hgrowth := globalFirstLaneExactTraced_query_encodingCountGrowth right.1.2 right.1.1 right.2
    (.inr request) rightState result hresult
  change cachedEncodingInputCount result.1.2.causalState.cache right.1.1.secretKey.parameter = _ at hgrowth
  rw [hcacheCount] at hgrowth
  have htraceLeft : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  have hsourceTrace := countedSourceImpl_encodingInputCount_update secretKey left.secretKey.parameter
    (.inr request) leftState source hsource
  simp only [attackerActionFragment_encodingInputCount, Nat.add_zero] at hsourceTrace
  have htargetTrace : result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter =
      rightState.attackerTrace.encodingInputCount right.1.1.secretKey.parameter := by
    rw [hresultEq, CappedChain.globalExactTracedNextState]
    change (rightState.attackerTrace ++ CappedChain.attackerActionFragment (.inr request) base.1.1).encodingInputCount
      right.1.1.secretKey.parameter = _
    simp only [CappedChain.AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount,
      Nat.add_zero]
  have hsamples : (history ++ result.2).encodingActions.length ≤
      result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter + source.2.counts.signing := by
    change cachedEncodingInputCount source.2.counts.cache left.secretKey.parameter ≤
      ((source.2.attackerTrace.encodingInputCount left.secretKey.parameter +
        source.2.counts.signing : Nat) : ℝ≥0∞) at hsourceEncoding
    rw [hsourceTrace, htraceLeft, hcacheEq, ← hfinalCache, ← hparameter, hgrowth] at hsourceEncoding
    rw [htargetTrace, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]
    exact_mod_cast hsourceEncoding
  have hfragment := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le right.1.2
    ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inr request)).run rightState)
    (CappedChain.directHashActionCost (.inr request))
    (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1 right.2 (.inr request) rightState)
    result hresult
  have hdirect := countedSourceImpl_direct_eq secretKey (.inr request) leftState source hsource
  change FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 at hfragment
  change source.2.counts.direct = leftState.counts.direct + 0 at hdirect
  unfold observableFirstLaneCharge CountedSourceState.charge at *
  constructor
  · omega
  · rw [FirstLaneOracleSimulation.hazardCount_append]
    omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_signing_charge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_signing_charge_bounds

end XmssSecurity.TargetSum.CappedChain

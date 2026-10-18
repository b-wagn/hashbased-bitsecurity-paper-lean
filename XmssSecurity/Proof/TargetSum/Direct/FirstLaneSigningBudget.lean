import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSigningSupport
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The observable budget holds through a supported signing step, including the step
that triggers a collision. Its proof uses a supported source witness, not an equality
between the executions after a hit. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem encodingInputCount_eq_of_globalSigning_agree
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : Generic.HashCachesAgreeOn (Generic.CappedChain.GlobalSigningComparableHashInput parameter) left right) :
    Generic.cachedEncodingInputCount left parameter = Generic.cachedEncodingInputCount right parameter := by
  apply cachedEncodingInputCount_eq_of_agree
  intro input hencoding
  obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨⟨message, randomness⟩, hinput⟩ :=
    Generic.exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex hleaf
  exact hagrees input ⟨leafIndex, message, randomness, hinput.symm⟩

theorem countedSourceImpl_encodingInputCount_update (secretKey : Generic.SecretKey)
    (parameter : PublicParameter) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : CountedSourceState) (result : (OracleWorld + Generic.SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.encodingInputCount parameter = state.attackerTrace.encodingInputCount parameter +
      (Generic.CappedChain.attackerActionFragment input result.1).encodingInputCount parameter := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact AttackerActionTrace.encodingInputCount_append parameter _ _

theorem firstLane_signing_charge_bounds {α : Type}
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (request : Generic.SignRequest) (next : Option Generic.Signature → OracleComp (OracleWorld + Generic.SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : Generic.CappedChain.GlobalHighDirectTracedState)
    (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hstate : Generic.CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : Generic.cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : Generic.FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Generic.Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + Generic.SigningSpec).query (.inr request)) >>= next) leftState)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inr request)).run rightState)).run)) :
    (leftState.counts.direct + 2 * ((history ++ result.2).encodingActions.length -
      result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  let secretKey := Generic.Concrete.materializePrecomputation left.cache left.secretKey
  have hparameter := Generic.CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  obtain ⟨monitor, _hobserved, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  obtain ⟨base, hbase, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose right.1.2 right.1.1
    (.inr request) (Generic.CappedChain.globalFirstLaneSigningImpl right.1.1 request) rightState result hresult
  obtain ⟨source, hsource, hagrees⟩ := exists_countedSource_signing_of_firstLane_support left right hrel
    hleftSupport hrightSupport leftState rightState.causalState hcausal request base hbase
  have hcharge := (hbudget.query_step source hsource).1
  have hsourceEncoding := countedSourceImpl_encodingBudget secretKey (.inr request) leftState
    hencoding source hsource
  have hcacheEq := encodingInputCount_eq_of_globalSigning_agree left.secretKey.parameter
    source.2.counts.cache base.1.2.cache hagrees
  have hfinalCache : result.1.2.causalState.cache = base.1.2.cache := by
    rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]
  have hgrowth := globalFirstLaneExactTraced_query_encodingCountGrowth right.1.2 right.1.1 right.2
    (.inr request) rightState result hresult
  change Generic.cachedEncodingInputCount result.1.2.causalState.cache right.1.1.secretKey.parameter = _ at hgrowth
  rw [hcacheCount] at hgrowth
  have htraceLeft : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  have hsourceTrace := countedSourceImpl_encodingInputCount_update secretKey left.secretKey.parameter
    (.inr request) leftState source hsource
  simp only [attackerActionFragment_encodingInputCount, Nat.add_zero] at hsourceTrace
  have htargetTrace : result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter =
      rightState.attackerTrace.encodingInputCount right.1.1.secretKey.parameter := by
    rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]
    change (rightState.attackerTrace ++ Generic.CappedChain.attackerActionFragment (.inr request) base.1.1).encodingInputCount
      right.1.1.secretKey.parameter = _
    simp only [AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount,
      Nat.add_zero]
  have hsamples : (history ++ result.2).encodingActions.length ≤
      result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter + source.2.counts.signing := by
    change Generic.cachedEncodingInputCount source.2.counts.cache left.secretKey.parameter ≤
      ((source.2.attackerTrace.encodingInputCount left.secretKey.parameter +
        source.2.counts.signing : Nat) : ℝ≥0∞) at hsourceEncoding
    rw [hsourceTrace, htraceLeft, hcacheEq, ← hfinalCache, ← hparameter, hgrowth] at hsourceEncoding
    rw [htargetTrace, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]
    exact_mod_cast hsourceEncoding
  have hfragment := Generic.FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le right.1.2
    ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inr request)).run rightState)
    (Generic.CappedChain.directHashActionCost (.inr request))
    (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1 right.2 (.inr request) rightState)
    result hresult
  have hdirect := countedSourceImpl_direct_eq secretKey (.inr request) leftState source hsource
  change Generic.FirstLaneOracleSimulation.hazardCount result.2 ≤ 0 at hfragment
  change source.2.counts.direct = leftState.counts.direct + 0 at hdirect
  unfold observableFirstLaneCharge CountedSourceState.charge at *
  constructor
  · omega
  · rw [Generic.FirstLaneOracleSimulation.hazardCount_append]
    omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_signing_charge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_signing_charge_bounds

end XmssSecurity.TargetSum.CappedChain

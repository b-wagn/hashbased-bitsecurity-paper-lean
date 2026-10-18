import XmssSecurity.Proof.Generic.Direct.DecidingProbe
import XmssSecurity.Proof.Generic.Direct.DecidingPrefixCoverage

/-! Transfer the first-lane event at an adversary prefix to the single public probe. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete CappedChain FirstLaneOracleSimulation

noncomputable def prefixProbeEncoding (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (forgery : Forgery) : Encoding :=
  (forgedEncoding cache parameter forgery).getD (fun _ => ⟨0, by decide⟩)

noncomputable def prefixProbeResult (table : GlobalChainValueIndex → Digest)
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (forgery : Forgery) :
    ChainIndex × ActionTrace GlobalChainValueIndex :=
  decidingProbeResult table forgery.epoch (signedEncoding cache parameter log forgery.epoch)
    (prefixProbeEncoding cache parameter forgery) forgery.signature.chainValue

def PrefixFirstLaneEvent (keyView : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) : Prop :=
  let cache := result.2.1.1.1
  let log := result.2.2.toSigningLog
  let encoding := prefixProbeEncoding cache keyView.secretKey.parameter result.1
  let chain := (prefixProbeResult keyView.table cache keyView.secretKey.parameter log result.1).1
  SigningTranscript.Valid log ∧
    (CappedEncodingMonitor.runObserved EncodingMonitor.State.empty result.2.1.2 = true ∨
      (¬ ProbeEligible (signedEncoding cache keyView.secretKey.parameter log result.1.epoch)
        encoding chain) ∧
      keyView.table (chain, result.1.epoch, encoding chain) = result.1.signature.chainValue chain ∧
      (chain, result.1.epoch, encoding chain) ∉
        GlobalReturnedChainValueCovered cache keyView.secretKey log)

theorem decodedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (leaf : LeafIndex) (input : Message × Randomness) :
    CacheView.decodedEncoding leftCache parameter leaf input =
      CacheView.decodedEncoding rightCache parameter leaf input :=
  CacheView.decodedEncoding_eq_of_input_eq (hcaches _ ⟨leaf, input.1, input.2, rfl⟩)

theorem signedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (log : QueryLog SigningSpec) (leaf : LeafIndex) :
    signedEncoding leftCache parameter log leaf = signedEncoding rightCache parameter log leaf := by
  unfold signedEncoding
  split
  · rfl
  · rw [decodedEncoding_eq_of_comparableCaches _ _ _ hcaches]

theorem prefixProbeEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (forgery : Forgery) :
    prefixProbeEncoding leftCache parameter forgery =
      prefixProbeEncoding rightCache parameter forgery := by
  unfold prefixProbeEncoding forgedEncoding
  rw [decodedEncoding_eq_of_comparableCaches _ _ _ hcaches]

theorem prefixFirstLaneEvent_good_implies_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (hkey : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftResult : Forgery × SourceExactTracedState)
    (rightResult : (Forgery × GlobalDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hforgery : leftResult.1 = rightResult.1.1)
    (hgood : SourceFirstLaneExactGoodStateRelation left right leftResult.2
      rightResult.1.2 rightResult.2)
    (hcovered : GlobalCausalTraceRevealsCovered
      (GlobalReturnedChainValueCovered rightResult.1.2.causalState.cache right.1.secretKey
        rightResult.1.2.attackerTrace.toSigningLog) rightResult.2.chainActions)
    (hevent : PrefixFirstLaneEvent left leftResult) :
    CombinedHit right.2 (rightResult.2 ++
      (prefixProbeResult right.2 rightResult.1.2.causalState.cache right.1.secretKey.parameter
        rightResult.1.2.attackerTrace.toSigningLog rightResult.1.1).2) := by
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hkey hleftSupport hrightSupport
  have htables : left.table = right.2 := hkey.1.toStable.1.1
  have htrace : leftResult.2.2 = rightResult.1.2.attackerTrace := hgood.1.2
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
  change GlobalFilteredCausalStateRelation left right leftResult.2.1.1.1
    rightResult.1.2.causalState at hcausal
  have hsigned : signedEncoding leftResult.2.1.1.1 left.secretKey.parameter
      leftResult.2.2.toSigningLog leftResult.1.epoch =
    signedEncoding rightResult.1.2.causalState.cache right.1.secretKey.parameter
      rightResult.1.2.attackerTrace.toSigningLog rightResult.1.1.epoch := by
    rw [hparameter, ← htrace, ← hforgery]
    exact signedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _ _
  have hencoding : prefixProbeEncoding leftResult.2.1.1.1 left.secretKey.parameter leftResult.1 =
    prefixProbeEncoding rightResult.1.2.causalState.cache right.1.secretKey.parameter
      rightResult.1.1 := by
    rw [hparameter, ← hforgery]
    exact prefixProbeEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
  have hprobe : prefixProbeResult left.table leftResult.2.1.1.1 left.secretKey.parameter
      leftResult.2.2.toSigningLog leftResult.1 =
    prefixProbeResult right.2 rightResult.1.2.causalState.cache right.1.secretKey.parameter
      rightResult.1.2.attackerTrace.toSigningLog rightResult.1.1 := by
    unfold prefixProbeResult
    rw [htables, hsigned, hencoding, hforgery]
  obtain ⟨hvalid, hencodingHit | ⟨hhidden, hvalue, huncovered⟩⟩ := hevent
  · apply CombinedHit.append_of_prefix
    exact globalExactEncodingEvent_implies_combinedHit right.2 leftResult.2.1.2
      rightResult.1.2.attackerTrace rightResult.2 hgood.2.1 hgood.2.2
      (htrace ▸ hvalid) hencodingHit
  · rw [hprobe, hsigned, hencoding] at hhidden
    rw [hprobe, hencoding, hforgery, htables] at hvalue
    rw [hprobe, hencoding, hforgery] at huncovered
    apply decidingProbeResult_hidden_hit _ _ _ _ _ _ hhidden
    · exact hvalue
    · intro value hmem
      apply huncovered
      apply globalReturnedChainValueCovered_of_comparableCaches left.secretKey.parameter
        leftResult.2.1.1.1 rightResult.1.2.causalState.cache left.secretKey right.1.secretKey
        leftResult.2.2.toSigningLog rightResult.1.2.attackerTrace.toSigningLog rfl hparameter
        (congrArg AttackerActionTrace.toSigningLog htrace.symm) hcausal.1
      exact hcovered _ value ((chainAction_mem_iff _ _).mpr hmem)

end XmssSecurity.Generic.Deciding

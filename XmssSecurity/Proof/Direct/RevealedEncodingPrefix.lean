import XmssSecurity.Proof.Direct.FreshRevealedConditioning

/-! The revealed-value witness with an explicitly supplied forged encoding. This
allows a fresh final encoding to be sampled after the adversary prefix. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open Concrete CappedChain Direct FirstLaneOracleSimulation

def RevealedEncodingPrefixEvent (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) (encoding : Encoding) : Prop :=
  let cache := result.2.1.1.1
  let log := result.2.2.toSigningLog
  let chain := (decidingProbeResult key.table result.1.epoch
    (signedEncoding cache key.secretKey.parameter log result.1.epoch)
    encoding result.1.signature.chainValue).1
  SigningTranscript.Valid log ∧
    ¬ProbeEligible (signedEncoding cache key.secretKey.parameter log result.1.epoch) encoding chain ∧
    key.table (chain, result.1.epoch, encoding chain) = result.1.signature.chainValue chain ∧
    (chain, result.1.epoch, encoding chain) ∉ GlobalReturnedChainValueCovered cache key.secretKey log

theorem revealedEncodingPrefixEvent_of_winning_revealed (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl (verificationPhase key.publicKey
      (materializePrecomputation key.cache key.secretKey)
        (prefixResult.1, prefixResult.2.2.toSigningLog))).run prefixResult.2.1.1.1))
    (hwin : execution.1.won = true)
    (hrevealed : DecidingChainValueRevealed execution.2 execution.1)
    (encoding : Encoding)
    (hdecode : forgedEncoding execution.2 execution.1.secretKey.parameter execution.1.forgery =
      some encoding) :
    RevealedEncodingPrefixEvent key prefixResult encoding := by
  let keyResult := materializeCachedKeyResult key.keyResult
  have hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅) :=
    Concrete.oldKeygen_support_materializedPrecomputedKeygen key.keyResult
      (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have hphase := sourcePrefixExecution_phase_support adversary key prefixResult hprefix
  have hfirst := xmssRom_cache_le _ key.cache _ hphase
  have hsecond := xmssRom_cache_le _ prefixResult.2.1.1.1 execution hafter
  obtain ⟨hpk, hsk, hforgery, hlog, _hverify⟩ := verificationPhase_support _ _ _ _ _ hafter
  dsimp only at hfirst hforgery hlog
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution (afterKeygen_of_phases adversary _ _ _ _ hphase execution hafter)
  have hconsistent := capped_detailed_execution_consistent adversary execution hgame
  have hchainEvent := (deciding_revealed_chain_event _ _ hconsistent hwin hrevealed).1
  obtain ⟨actual, hactual, hbelow, hvalue⟩ := hrevealed
  rw [hdecode] at hactual
  cases hactual
  have hsigned := signedEncoding_eq_of_cache_le _ _ hsecond keyResult.1.2
    prefixResult.2.2.toSigningLog (adversaryPhase_signingLog_consistent adversary keyResult hkeygen
      ((prefixResult.1, prefixResult.2.2.toSigningLog), prefixResult.2.1.1.1) hphase) prefixResult.1.epoch
  change signedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.2.2.toSigningLog
    prefixResult.1.epoch = signedEncoding execution.2 key.secretKey.parameter
      prefixResult.2.2.toSigningLog prefixResult.1.epoch at hsigned
  have hchain := outcomeDecidingChain_eq execution.2 execution.1 encoding hdecode
  have hchosen : (decidingProbeResult key.table prefixResult.1.epoch
      (signedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.2.2.toSigningLog
        prefixResult.1.epoch) encoding prefixResult.1.signature.chainValue).1 =
      outcomeDecidingChain execution.2 execution.1 := by
    rw [hsigned, hchain, hsk, hlog, hforgery]
    exact decidingSearchResult_eq_decidingChain key.table execution.2
      (materializePrecomputation key.cache key.secretKey) prefixResult.2.2.toSigningLog prefixResult.1 encoding
      (fun chain => keyView_honestChainValue_eq_table key hkey _ (hfirst.trans hsecond) _ chain _)
  change SigningTranscript.Valid _ ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hlog]
    exact (execution.1.won_eq_true_iff.mp hwin).1
  · rw [hchosen, hchain]
    rintro ⟨signed, hsignedPrefix, hle⟩
    have hsignedFinal : signedEncoding execution.2 execution.1.secretKey.parameter
        execution.1.signingLog execution.1.forgery.epoch = some signed := by
      rw [hsk, hlog, hforgery]
      change signedEncoding execution.2 key.secretKey.parameter prefixResult.2.2.toSigningLog
        prefixResult.1.epoch = some signed
      rw [← hsigned]
      exact hsignedPrefix
    exact (not_lt_of_ge hle) (hbelow signed hsignedFinal)
  · rw [hchosen, hchain]
    rw [← keyView_honestChainValue_eq_table key hkey execution.2 (hfirst.trans hsecond)]
    simpa only [hsk, hforgery] using hvalue.symm
  · rw [hchosen]
    intro hmem
    have hmemFinal := globalReturnedChainValueCovered_mono_cache _ _ hsecond key.secretKey
      prefixResult.2.2.toSigningLog _ hmem
    have hnot := hchainEvent.forged_chain_coordinate_not_mem_returned encoding hdecode
    apply hnot
    rw [XmssSecurity.mem_returnedChainValueIndices_iff]
    change (_, _) ∈ ReturnedChainValueCovered _ _ _ _ at hmemFinal
    rw [returnedChainValueCovered_iff] at hmemFinal
    simpa only [hsk, hlog, hforgery, materializePrecomputation, precomputedSecretKey] using hmemFinal

theorem sourcePrefixFinishAfterHash_revealed_implies_prefixEvent (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (output : Checksum.AcceptedHashOutput)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult))
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinishAfterHash key prefixResult output.1))
    (hevent : SourceWinningRevealedEvent (key, execution)) :
    RevealedEncodingPrefixEvent key prefixResult (Checksum.acceptedHashEncoding output) := by
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [sourcePrefixFinishAfterHash, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  have hverify : verified ∈ support ((simulateQ romImpl (Concrete.scheme.verify key.publicKey
      prefixResult.1.epoch prefixResult.1.message prefixResult.1.signature)).run prefixResult.2.1.1.1) := by
    rw [verify_run_fresh _ _ _ _ _ hfresh, mem_support_bind_iff]
    exact ⟨output.1, by simp, hverified⟩
  let outcome : GameOutcome := ⟨key.publicKey, materializePrecomputation key.cache key.secretKey,
    prefixResult.1, prefixResult.2.2.toSigningLog, verified.1⟩
  have hafter : (outcome, verified.2) ∈ support ((simulateQ romImpl
      (verificationPhase key.publicKey (materializePrecomputation key.cache key.secretKey)
        (prefixResult.1, prefixResult.2.2.toSigningLog))).run prefixResult.2.1.1.1) := by
    unfold verificationPhase
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨verified, hverify, by simp [outcome]⟩
  have hcacheLe := Concrete.CacheReplay.randomOracle_cache_le _ _ verified hverified
  have houtput : verified.2 (forgeryEncodingInput key.publicKey prefixResult.1) = some output.1 :=
    hcacheLe (QueryCache.cacheQuery_self _ _ _)
  have hparameter := keygen_parameter_eq key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  change key.publicKey.parameter = key.secretKey.parameter at hparameter
  have hdecode : forgedEncoding verified.2 outcome.secretKey.parameter outcome.forgery =
      some (Checksum.acceptedHashEncoding output) := by
    change CacheView.decodedEncoding verified.2 key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness) = _
    change verified.2 (CacheView.encodingInput key.publicKey.parameter prefixResult.1.epoch
      (prefixResult.1.message, prefixResult.1.signature.randomness)) = some output.1 at houtput
    rw [hparameter] at houtput
    rw [CacheView.encodingHash, CacheView.digestAt_eq_of_cache_eq_some houtput]
    exact Checksum.acceptedHashEncoding_decode output
  apply revealedEncodingPrefixEvent_of_winning_revealed adversary key hkey prefixResult hprefix
    (outcome, verified.2) hafter _ _ _ hdecode
  · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
      sourceGlobalExactExecutionResult, hlogs] using hevent.1
  · simpa only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
      sourceGlobalExactExecutionResult, hlogs] using hevent.2

theorem revealedEncodingPrefixEvent_good_implies_hit
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (source : Forgery × SourceExactTracedState)
    (target : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hforgery : source.1 = target.1.1)
    (hgood : SourceFirstLaneExactGoodStateRelation left right.1 source.2 target.1.2 target.2)
    (hcovered : GlobalCausalTraceRevealsCovered
      (GlobalReturnedChainValueCovered target.1.2.causalState.cache right.1.1.secretKey
        target.1.2.attackerTrace.toSigningLog) target.2.chainActions)
    (encoding : Encoding) (hevent : RevealedEncodingPrefixEvent left source encoding) :
    CombinedHit right.1.2 (target.2 ++
      (decidingProbeResult right.1.2 target.1.1.epoch
        (signedEncoding target.1.2.causalState.cache right.1.1.secretKey.parameter
          target.1.2.attackerTrace.toSigningLog target.1.1.epoch)
        encoding target.1.1.signature.chainValue).2) := by
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hkey hleft hright
  have htables : left.table = right.1.2 := hkey.1.toStable.1.1
  have htrace : source.2.2 = target.1.2.attackerTrace := hgood.1.2
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
  change GlobalFilteredCausalStateRelation left right.1 source.2.1.1.1 target.1.2.causalState at hcausal
  have hsigned : signedEncoding source.2.1.1.1 left.secretKey.parameter source.2.2.toSigningLog source.1.epoch =
      signedEncoding target.1.2.causalState.cache right.1.1.secretKey.parameter
        target.1.2.attackerTrace.toSigningLog target.1.1.epoch := by
    rw [hparameter, ← htrace, ← hforgery]
    exact signedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _ _
  obtain ⟨_hvalid, hhidden, hvalue, huncovered⟩ := hevent
  rw [htables, hsigned, hforgery] at hhidden hvalue huncovered
  apply decidingProbeResult_hidden_hit _ _ _ _ _ _ hhidden hvalue
  intro value hmem
  apply huncovered
  apply globalReturnedChainValueCovered_of_comparableCaches left.secretKey.parameter
    source.2.1.1.1 target.1.2.causalState.cache left.secretKey right.1.1.secretKey
    source.2.2.toSigningLog target.1.2.attackerTrace.toSigningLog rfl hparameter
    (congrArg AttackerActionTrace.toSigningLog htrace.symm) hcausal.1
  exact hcovered _ value ((chainAction_mem_iff _ _).mpr hmem)

/-- info: 'XmssSecurity.Deciding.revealedEncodingPrefixEvent_good_implies_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms revealedEncodingPrefixEvent_good_implies_hit

/-- info: 'XmssSecurity.Deciding.sourcePrefixFinishAfterHash_revealed_implies_prefixEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixFinishAfterHash_revealed_implies_prefixEvent

end XmssSecurity.Deciding

import XmssSecurity.Proof.Generic.Direct.DecidingPrefixProjection
import XmssSecurity.Proof.Generic.Direct.DecidingRevealed

/-! Hidden deciding values in a winning verification were already fixed in its adversary prefixResult. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete CappedChain

theorem globalReturnedChainValueCovered_mono_cache (initialCache finalCache : QueryCache HashSpec)
    (hle : initialCache ≤ finalCache) (secretKey : SecretKey) (log : QueryLog SigningSpec)
    (index : GlobalChainValueIndex)
    (hmem : index ∈ GlobalReturnedChainValueCovered initialCache secretKey log) :
    index ∈ GlobalReturnedChainValueCovered finalCache secretKey log := by
  change index.2 ∈ ReturnedChainValueCovered _ _ _ index.1 at hmem ⊢
  rw [returnedChainValueCovered_iff] at hmem ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode, hleaf, hdigit⟩ := hmem
  refine ⟨request, signature, encoding, hreturned, ?_, hleaf, hdigit⟩
  obtain ⟨output, houtput⟩ := CacheView.encodingInput_cached_of_decode_some initialCache
    secretKey.parameter request.epoch request.message signature.randomness encoding hdecode
  rw [← CacheView.decodedEncoding_eq_of_input_eq (houtput.trans (hle houtput).symm)]
  exact hdecode

theorem keyView_honestChainValue_eq_table (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (cache : QueryCache HashSpec) (hle : key.cache ≤ cache)
    (leaf : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    honestChainValue cache (materializePrecomputation key.cache key.secretKey) leaf chain digit =
      key.table (chain, leaf, digit) := by
  have hmaterialized := Concrete.oldKeygen_support_materializedPrecomputedKeygen key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have hstable := honestChainValue_eq_of_keygen_cache_le _ hmaterialized cache key.cache hle
    le_rfl leaf chain digit
  change honestChainValue cache (materializePrecomputation key.cache key.secretKey) leaf chain digit =
    honestChainValue key.cache (materializePrecomputation key.cache key.secretKey) leaf chain digit
    at hstable
  rw [hstable]
  have htable := congrFun (trajectoryProgrammedGlobalChainKeygen_support_table key hkey)
    (chain, leaf, digit)
  simpa only [honestChainValue, materializePrecomputation_parameter,
    materializePrecomputation_chainStart, globalKeygenChainValueTable,
    CappedChain.keygenChainValueTable, Wots.signChain] using htable

theorem prefixFirstLaneEvent_of_winning_revealed (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter prefixResult.1.epoch
      (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl (verificationPhase key.publicKey
      (materializePrecomputation key.cache key.secretKey)
        (prefixResult.1, prefixResult.2.2.toSigningLog))).run prefixResult.2.1.1.1))
    (hwin : execution.1.won = true)
    (hrevealed : DecidingChainValueRevealed execution.2 execution.1) :
    PrefixFirstLaneEvent key prefixResult := by
  let keyResult := materializeCachedKeyResult key.keyResult
  have hparameter : keyResult.1.2.parameter = key.secretKey.parameter :=
    materializePrecomputation_parameter key.cache key.secretKey
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
  obtain ⟨encoding, hdecode, hbelow, hvalue⟩ := hrevealed
  have hdecodePrefix : forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1 =
      some encoding := by
    rw [forgedEncoding_eq_of_cache_le _ _ hsecond _ _ hcached]
    simpa only [hsk, hforgery, materializePrecomputation_parameter] using hdecode
  have hprefixEncoding : prefixProbeEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1 =
      encoding := by simp only [prefixProbeEncoding, hdecodePrefix, Option.getD_some]
  have hchosen : (prefixProbeResult key.table prefixResult.2.1.1.1 key.secretKey.parameter
      prefixResult.2.2.toSigningLog prefixResult.1).1 = outcomeDecidingChain execution.2 execution.1 := by
    unfold prefixProbeResult
    rw [hprefixEncoding]
    have hselected := decidingSearchResult_eq_decidingChain key.table prefixResult.2.1.1.1
      (materializePrecomputation key.cache key.secretKey) prefixResult.2.2.toSigningLog prefixResult.1 encoding
      (fun chain => keyView_honestChainValue_eq_table key hkey _ hfirst _ chain _)
    simp only [materializePrecomputation_parameter] at hselected
    have hstable := outcomeDecidingChain_prefix_eq_final adversary keyResult hkeygen
      ((prefixResult.1, prefixResult.2.2.toSigningLog), prefixResult.2.1.1.1) hphase
      (by rw [hparameter]; exact hcached) execution hafter
    have hprefixChain := outcomeDecidingChain_eq prefixResult.2.1.1.1
      (⟨keyResult.1.1, keyResult.1.2, prefixResult.1, prefixResult.2.2.toSigningLog, false⟩ : GameOutcome)
      encoding (by dsimp only; rw [hparameter]; exact hdecodePrefix)
    exact hselected.trans (hprefixChain.symm.trans hstable)
  have hsigned := signedEncoding_eq_of_cache_le _ _ hsecond keyResult.1.2
    prefixResult.2.2.toSigningLog (adversaryPhase_signingLog_consistent adversary keyResult hkeygen
      ((prefixResult.1, prefixResult.2.2.toSigningLog), prefixResult.2.1.1.1) hphase) prefixResult.1.epoch
  rw [hparameter] at hsigned
  have hchain : outcomeDecidingChain execution.2 execution.1 =
      decidingChain execution.2 execution.1.secretKey execution.1.signingLog execution.1.forgery
        encoding := outcomeDecidingChain_eq _ _ encoding hdecode
  refine ⟨?_, Or.inr ⟨?_, ?_, ?_⟩⟩
  · rw [← hlog]
    exact (execution.1.won_eq_true_iff.mp hwin).1
  · rw [hprefixEncoding, hchosen, hchain]
    rintro ⟨signed, hsignedPrefix, hle⟩
    have hsignedFinal : signedEncoding execution.2 execution.1.secretKey.parameter
        execution.1.signingLog execution.1.forgery.epoch = some signed := by
      rw [hsk, hlog, hforgery, materializePrecomputation_parameter]
      rw [← hsigned]
      exact hsignedPrefix
    exact (not_lt_of_ge hle) (hbelow signed hsignedFinal)
  · rw [hchosen, hprefixEncoding, hchain]
    rw [← keyView_honestChainValue_eq_table key hkey execution.2 (hfirst.trans hsecond)]
    simpa only [hsk, hforgery] using hvalue.symm
  · rw [hchosen, hprefixEncoding]
    intro hmem
    have hmemFinal := globalReturnedChainValueCovered_mono_cache _ _ hsecond key.secretKey
      prefixResult.2.2.toSigningLog _ hmem
    have hnot := hchainEvent.forged_chain_coordinate_not_mem_returned encoding hdecode
    apply hnot
    rw [XmssSecurity.Generic.mem_returnedChainValueIndices_iff]
    change (_, _) ∈ ReturnedChainValueCovered _ _ _ _ at hmemFinal
    rw [returnedChainValueCovered_iff] at hmemFinal
    simpa only [hsk, hlog, hforgery, materializePrecomputation_parameter] using hmemFinal

end XmssSecurity.Generic.Deciding

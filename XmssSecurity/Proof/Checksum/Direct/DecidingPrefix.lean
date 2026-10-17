import XmssSecurity.Proof.Checksum.Direct.DecidingClassification
import XmssSecurity.Proof.Checksum.Direct.DecidingCache

/-! The deciding chain is fixed before verification once the forged encoding has been queried. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.Deciding

open Concrete

theorem adversaryPhase_signingLog_consistent (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2)) :
    SigningLogConsistent prefixResult.2 keyResult.1.2 prefixResult.1.2 := by
  have hkeygenLe := xmssRom_cache_le _ keyResult.2 prefixResult hprefix
  apply cappedMappedAdversary_signingLog_consistent keyResult.1.1 keyResult.1.2
    (adversary.main keyResult.1.1) keyResult.2 prefixResult _ keyResult.2 prefixResult.2
    (precomputedKeygen_support_consistent keyResult hkeygen) hkeygenLe le_rfl
  rw [cappedMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run]
  exact hprefix

theorem encodingHash_eq_of_cached (initialCache finalCache : QueryCache HashSpec)
    (hle : initialCache ≤ finalCache) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness)
    (hcached : initialCache (CacheView.encodingInput parameter leafIndex input) ≠ none) :
    CacheView.encodingHash initialCache parameter leafIndex input =
      CacheView.encodingHash finalCache parameter leafIndex input := by
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists.mp hcached
  exact (CacheView.digestAt_eq_of_cache_eq_some houtput.symm).trans
    (CacheView.digestAt_eq_of_cache_eq_some (hle houtput.symm)).symm

theorem signedEncoding_eq_of_cache_le (initialCache finalCache : QueryCache HashSpec)
    (hle : initialCache ≤ finalCache) (secretKey : SecretKey) (log : QueryLog SigningSpec)
    (hlog : SigningLogConsistent initialCache secretKey log) (leafIndex : LeafIndex) :
    signedEncoding initialCache secretKey.parameter log leafIndex =
      signedEncoding finalCache secretKey.parameter log leafIndex := by
  cases hreturned : returnedAt log leafIndex with
  | none => simp only [signedEncoding, hreturned]
  | some pair =>
    rcases pair with ⟨request, signature⟩
    obtain ⟨hentry, hepoch⟩ := returned_of_returnedAt _ _ _ _ hreturned
    obtain ⟨encoding, hdecode, _⟩ := hlog request signature hentry
    obtain ⟨output, houtput⟩ := CacheView.encodingInput_cached_of_decode_some initialCache
      secretKey.parameter request.epoch request.message signature.randomness encoding hdecode
    rw [hepoch] at houtput
    have hdec : CacheView.decodedEncoding initialCache secretKey.parameter leafIndex
        (request.message, signature.randomness) =
        CacheView.decodedEncoding finalCache secretKey.parameter leafIndex
          (request.message, signature.randomness) :=
      CacheView.decodedEncoding_eq_of_input_eq (houtput.trans (hle houtput).symm)
    simp only [signedEncoding, hreturned, hdec]

theorem forgedEncoding_eq_of_cache_le (initialCache finalCache : QueryCache HashSpec)
    (hle : initialCache ≤ finalCache) (parameter : PublicParameter) (forgery : Forgery)
    (hcached : initialCache (CacheView.encodingInput parameter forgery.epoch
      (forgery.message, forgery.signature.randomness)) ≠ none) :
    forgedEncoding initialCache parameter forgery = forgedEncoding finalCache parameter forgery := by
  unfold forgedEncoding
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists.mp hcached
  exact CacheView.decodedEncoding_eq_of_input_eq (houtput.symm.trans (hle houtput.symm).symm)

theorem honestChainValue_eq_of_keygen_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (initialCache finalCache : QueryCache HashSpec)
    (hinitial : keyResult.2 ≤ initialCache) (hfinal : keyResult.2 ≤ finalCache)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    honestChainValue initialCache keyResult.1.2 leafIndex chain digit =
      honestChainValue finalCache keyResult.1.2 leafIndex chain digit :=
  (precomputedKeygen_chainWalk_eq_of_cache_le keyResult hkeygen initialCache hinitial leafIndex
    chain digit.val (Nat.le_pred_of_lt digit.isLt)).symm.trans
      (precomputedKeygen_chainWalk_eq_of_cache_le keyResult hkeygen finalCache hfinal leafIndex
        chain digit.val (Nat.le_pred_of_lt digit.isLt))

/-- Once the forged encoding is cached, the selected chain is unchanged by verification. -/
theorem outcomeDecidingChain_prefix_eq_final (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hcached : prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter prefixResult.1.1.epoch
      (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2)) :
    outcomeDecidingChain prefixResult.2
        ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩ =
      outcomeDecidingChain execution.2 execution.1 := by
  obtain ⟨hpk, hsk, hforgery, hlog, _⟩ := verificationPhase_support _ _ _ _ _ hafter
  have hfirst := xmssRom_cache_le _ keyResult.2 prefixResult hprefix
  have hsecond := xmssRom_cache_le _ prefixResult.2 execution hafter
  have hencoding := forgedEncoding_eq_of_cache_le prefixResult.2 execution.2 hsecond
    keyResult.1.2.parameter prefixResult.1.1 hcached
  unfold outcomeDecidingChain
  simp only [hsk, hforgery, hlog]
  rw [hencoding]
  split
  · rfl
  · apply decidingChain_congr
    · exact signedEncoding_eq_of_cache_le prefixResult.2 execution.2 hsecond keyResult.1.2 _
        (adversaryPhase_signingLog_consistent adversary keyResult hkeygen prefixResult hprefix) _
    · intro chain digit
      exact honestChainValue_eq_of_keygen_cache_le keyResult hkeygen prefixResult.2 execution.2
        hfirst (hfirst.trans hsecond) _ chain digit

end XmssSecurity.Checksum.Deciding

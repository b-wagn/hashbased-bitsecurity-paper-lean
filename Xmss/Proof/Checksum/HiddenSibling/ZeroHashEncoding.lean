import Xmss.Proof.Checksum.HiddenSibling.Signed
import Xmss.Proof.Generic.Direct.ReusedEncoding
import Xmss.Proof.Generic.Direct.DecidingRevealed

/-! With no adversary hash queries, a cached valid encoding input must have been signed. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

open Generic.Deciding

theorem realRun_zeroHash_encoding_source {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hzero : computation.IsQueryBoundP Direct.IsDirectHashQuery 0)
    (cache : QueryCache HashSpec) (leaf : LeafIndex) (payload : Message × Randomness)
    (hnone : cache (CacheView.encodingInput secretKey.parameter leaf payload) = none)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hresult : result ∈ support (realRun secretKey computation cache))
    (encoding : Generic.Encoding)
    (hdecode : CacheView.decodedEncoding result.2 secretKey.parameter leaf payload =
      some encoding) :
    ∃ request signature, SigningTranscript.Returned result.1.2 request signature ∧
      CacheView.encodingInput secretKey.parameter request.epoch
        (request.message, signature.randomness) =
      CacheView.encodingInput secretKey.parameter leaf payload := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [realRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [CacheView.decodedEncoding, hnone] at hdecode
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hzero
      have hnot : ¬ Direct.IsDirectHashQuery input := hzero.1.resolve_right (by omega)
      unfold realRun at hresult
      rw [Direct.run_logged_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hrest⟩ := hresult
      rw [support_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      rcases input with (uniform | hash) | request
      · rw [show (forwardOracles + signingOracle precomputedScheme secretKey) (.inl (.inl uniform)) =
            forwardOracles (.inl uniform) from rfl,
          romImpl_forwardOracles_run, romImpl_uniformFaithful, support_map] at hstep
        obtain ⟨sample, hsample, heq⟩ := hstep
        rw [support_map] at hsample
        obtain ⟨answer, _, rfl⟩ := hsample
        subst step
        simpa using ih answer (by simpa [Direct.IsDirectHashQuery] using hzero.2 answer)
          cache hnone rest hrest hdecode
      · exact (hnot rfl).elim
      · have hrun : (signingOracle precomputedScheme secretKey request).run =
            (fun answer => (answer, [⟨request, answer⟩])) <$>
              precomputedScheme.sign secretKey request.epoch request.message :=
          withLogging_run_eq _ request
        change step ∈ support ((simulateQ romImpl
          (signingOracle precomputedScheme secretKey request).run).run cache) at hstep
        rw [hrun, simulateQ_map, StateT.run_map, support_map] at hstep
        obtain ⟨answer, hanswer, rfl⟩ := hstep
        by_cases hsame : ∃ signature, answer.1 = some signature ∧
            CacheView.encodingInput secretKey.parameter request.epoch
              (request.message, signature.randomness) =
            CacheView.encodingInput secretKey.parameter leaf payload
        · obtain ⟨signature, hsignature, hinput⟩ := hsame
          refine ⟨request, signature, ?_, hinput⟩
          refine ⟨⟨request, answer.1⟩, ?_, rfl, hsignature⟩
          simp
        · have hle : answer.2 ≤ rest.2 := xmssRom_cache_le _ answer.2 rest hrest
          have hmiddle : answer.2 (CacheView.encodingInput secretKey.parameter leaf
              payload) = none :=
            Signing.precomputedCappedSign_preserves_later_valid_other_encodingInput secretKey
              request.epoch leaf request.message payload cache answer.2 rest.2 answer.1 hanswer
              hle encoding hdecode (fun signature hsig heq => hsame ⟨signature, hsig, heq⟩) hnone
          obtain ⟨req, sig, hreturned, hinput⟩ := ih answer.1
            (by simpa [Direct.IsDirectHashQuery] using hzero.2 answer.1)
            answer.2 hmiddle rest hrest hdecode
          refine ⟨req, sig, ?_, hinput⟩
          obtain ⟨entry, hentry, hrequest, hsignature⟩ := hreturned
          exact ⟨entry, List.mem_append_right _ hentry, hrequest, hsignature⟩

theorem zeroHash_cached_encoding_reuses (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (before : (Generic.Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hbefore : before ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hvalid : SigningTranscript.Valid before.1.2)
    (hcached : before.2 (CacheView.encodingInput keyResult.1.2.parameter before.1.1.epoch
      (before.1.1.message, before.1.1.signature.randomness)) ≠ none) :
    returnedAt before.1.2 before.1.1.epoch ≠ none ∧
      ReusesEncodingInput before.1.2 before.1.1 := by
  obtain ⟨digest, hdigest⟩ := Option.ne_none_iff_exists.mp hcached
  have hdecode : CacheView.decodedEncoding before.2 keyResult.1.2.parameter before.1.1.epoch
      (before.1.1.message, before.1.1.signature.randomness) = some (encode digest) := by
    unfold CacheView.decodedEncoding
    rw [← hdigest]
    rfl
  have hnone := Keygen.precomputedKeygen_cache_none_encodingInput keyResult hkey
    before.1.1.epoch (before.1.1.message, before.1.1.signature.randomness)
  obtain ⟨request, signature, hreturned, hinput⟩ := realRun_zeroHash_encoding_source
    keyResult.1.2 (adversary.main keyResult.1.1) (hzero keyResult.1.1) keyResult.2 before.1.1.epoch
    (before.1.1.message, before.1.1.signature.randomness) hnone before hbefore (encode digest) hdecode
  obtain ⟨hepoch, hpayload⟩ := (CacheView.encodingInput_eq_iff _ _ _ _ _).mp hinput
  constructor
  · intro hnone
    exact no_returned_of_returnedAt_none _ _ hnone ⟨request, signature, hreturned, hepoch⟩
  · intro other answer hother hotherEpoch
    obtain ⟨hrequest, hsignature⟩ := SigningTranscript.returned_eq_of_same_leafIndex hvalid
      hother hreturned (hotherEpoch.trans hepoch.symm)
    rw [hrequest, hsignature]
    exact hpayload

end Xmss.Checksum.HiddenSibling

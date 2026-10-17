import XmssSecurity.Proof.TargetSum.EncodingTargetMap
import XmssSecurity.Proof.TargetSum.SigningCacheTrace
import XmssSecurity.Proof.TargetSum.WinningEventReduction

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

/-- A winning encoding event identifies a genuine returned signature and a distinct forged encoding input with the same cached 128-bit digest. Its transcript contains at most one request per leaf index. -/
theorem winning_encoding_event_has_signed_collision
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    SigningTranscript.Valid outcome.signingLog ∧
    outcome.signingLog.length ≤ lifetime ∧
    ∃ request signature signedOutput forgedOutput,
      SigningTranscript.Returned outcome.signingLog request signature ∧
      request.epoch = outcome.forgery.epoch ∧
      Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness) ≠
        Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some signedOutput ∧
      cache (Concrete.CacheView.encodingInput outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some forgedOutput ∧
      truncateHash signedOutput = truncateHash forgedOutput ∧
      ∃ encoding, TargetSum.decodeDigest (truncateHash signedOutput) = some encoding := by
  refine ⟨hevent.signingTranscript_valid,
    hevent.signingLog_length_le_lifetime, ?_⟩
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨request, signature, signedEncoding, forgedEncoding, hsignedDecode,
      hforgedDecode, hreturned, hleafIndex, hencoding⟩ := hsame
    change (request.message, signature.randomness) ≠
        (outcome.forgery.message, outcome.forgery.signature.randomness) ∧
      Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness) =
        Concrete.CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) at hencoding
    obtain ⟨signedOutput, hsignedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch request.message signature.randomness
        signedEncoding hsignedDecode
    obtain ⟨forgedOutput, hforgedCached⟩ :=
      Concrete.CacheView.encodingInput_cached_of_decode_some cache
        outcome.secretKey.parameter request.epoch outcome.forgery.message
        outcome.forgery.signature.randomness forgedEncoding hforgedDecode
    refine ⟨request, signature, signedOutput, forgedOutput, hreturned, hleafIndex, ?_,
      hsignedCached, hforgedCached, ?_, ?_⟩
    · intro hinput
      exact hencoding.1
        (Concrete.CacheView.encodingInput_injective outcome.secretKey.parameter request.epoch
          hinput)
    · rw [Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hsignedCached,
        Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hforgedCached] at hencoding
      exact hencoding.2
    · rw [Concrete.CacheView.encodingHash,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hsignedCached] at hsignedDecode
      exact ⟨signedEncoding, hsignedDecode⟩
  · simp [Concrete.FreshLeafIndexBadEventOccurs,
      XmssSecurity.TargetSum.FreshLeafIndexBadEventOccurs] at hfresh

/-- A winning encoding collision is oriented at the matching signing boundary: either the forged encoding input was already cached before signing, or it was still fresh when the signer installed the honest target. -/
theorem winning_encoding_event_trace_temporal_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace, entry.PrehitPartnered outcome.secretKey cache ∧
      (entry.PreexistingEncodingCollision outcome.secretKey ∨
        entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache) := by
  obtain ⟨_hvalid, _hlength, request, signature, signedOutput, forgedOutput,
    hreturned, hleafIndex, hne, hsigned, hforged, hdigest, hsignedValid⟩ :=
    winning_encoding_event_has_signed_collision cache outcome hevent
  have hreturnedTrace :
      SigningTranscript.Returned trace.toSigningLog request signature := by
    rw [hlog]
    exact hreturned
  obtain ⟨entry, hentry, hrequest, hsignature⟩ :=
    (SigningTranscript.returned_toSigningLog_iff trace request signature).mp
      hreturnedTrace
  subst request
  obtain ⟨localSignedOutput, hlocalSigned⟩ :=
    hcached entry hentry signature hsignature
  have hlocalFinal := (hcaches entry hentry).2 hlocalSigned
  have houtput : localSignedOutput = signedOutput :=
    Option.some.inj (hlocalFinal.symm.trans hsigned)
  subst localSignedOutput
  let forgedInput := Concrete.CacheView.encodingInput outcome.secretKey.parameter
    outcome.forgery.epoch
      (outcome.forgery.message, outcome.forgery.signature.randomness)
  have hforgedFinal : cache forgedInput = some forgedOutput := by
    dsimp [forgedInput]
    rw [← hleafIndex]
    exact hforged
  have hdistinct :
      Concrete.CacheView.encodingInput outcome.secretKey.parameter entry.request.epoch
          (entry.request.message, signature.randomness) ≠ forgedInput := by
    dsimp [forgedInput]
    rw [← hleafIndex]
    exact hne
  have hpartnered : entry.PrehitPartnered outcome.secretKey cache := by
    refine ⟨signature, signedOutput, hsignature, hsigned, hsignedValid,
      (outcome.forgery.message, outcome.forgery.signature.randomness), ?_, forgedOutput, hforged,
      hdigest.symm⟩
    intro heq
    exact hne (congrArg (Concrete.CacheView.encodingInput outcome.secretKey.parameter
      entry.request.epoch) heq.symm)
  cases hinitial : entry.initialCache forgedInput with
  | none =>
      refine ⟨entry, hentry, hpartnered, Or.inr ?_⟩
      refine ⟨signature, signedOutput, forgedOutput, hsignature, hleafIndex,
        hinitial, hlocalSigned, hforgedFinal, hdistinct, hdigest⟩
  | some oldOutput =>
      have holdFinal := (hcaches entry hentry).1 hinitial
      have holdOutput : oldOutput = forgedOutput :=
        Option.some.inj (holdFinal.symm.trans hforgedFinal)
      subst oldOutput
      refine ⟨entry, hentry, hpartnered, Or.inl ?_⟩
      refine ⟨signature, signedOutput,
        (outcome.forgery.message, outcome.forgery.signature.randomness),
        forgedOutput, hsignature, hlocalSigned, ?_, ?_, hdigest⟩
      · rw [hleafIndex]
        exact hinitial
      · intro heq
        apply hdistinct
        dsimp [forgedInput]
        rw [← hleafIndex]
        exact congrArg
          (Concrete.CacheView.encodingInput outcome.secretKey.parameter
            entry.request.epoch) heq.symm

/-- The two budget classes are a pre-hit on the 128-bit signing randomness and a 128-bit digest collision, with the latter covering both temporal orientations around signing. -/
theorem winning_encoding_event_trace_monitor_decomposition
    (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (trace : SigningCacheTrace)
    (hlog : trace.toSigningLog = outcome.signingLog)
    (hcaches : trace.CachesLe cache)
    (hcached : trace.SuccessfulEncodingsCached outcome.secretKey)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ entry ∈ trace, entry.PrehitPartnered outcome.secretKey cache ∧
      (entry.EncodingInputPrehit outcome.secretKey ∨
        entry.FreshSigningEncodingCollision outcome.secretKey ∨
          entry.FreshForgedEncodingCollision outcome.secretKey outcome.forgery cache) := by
  obtain ⟨entry, hentry, hpartnered, hpreexisting | hfresh⟩ :=
    winning_encoding_event_trace_temporal_decomposition cache outcome trace
      hlog hcaches hcached hevent
  · rcases entry.preexistingEncodingCollision_cases outcome.secretKey hpreexisting with
      hprehit | hcollision
    · exact ⟨entry, hentry, hpartnered, Or.inl hprehit⟩
    · exact ⟨entry, hentry, hpartnered, Or.inr (Or.inl hcollision)⟩
  · exact ⟨entry, hentry, hpartnered, Or.inr (Or.inr hfresh)⟩

end XmssSecurity.TargetSum

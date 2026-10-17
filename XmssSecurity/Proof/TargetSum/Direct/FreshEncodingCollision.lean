import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.AdaptiveFreshTarget

/-! A fresh forged encoding can collide with only the one signed encoding at its
leaf. The corresponding signature must already supply an accepted prefix encoding. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open Concrete Direct

theorem winning_encoding_event_signed_target (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hevent : WinningOutcomeBadEventOccurs cache outcome .encoding) :
    ∃ request signature, returnedAt outcome.signingLog outcome.forgery.epoch = some (request, signature) ∧
      CacheView.encodingHash cache outcome.secretKey.parameter outcome.forgery.epoch
        (outcome.forgery.message, outcome.forgery.signature.randomness) =
      CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
        (request.message, signature.randomness) := by
  rcases hevent.2.2 with hsame | hfresh
  · obtain ⟨request, signature, signed, forged, _hsigned, _hforged, hentry, hepoch, hcollision⟩ := hsame
    change _ ≠ _ ∧ CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
      (request.message, signature.randomness) = CacheView.encodingHash cache outcome.secretKey.parameter
        request.epoch (outcome.forgery.message, outcome.forgery.signature.randomness) at hcollision
    cases hreturned : returnedAt outcome.signingLog outcome.forgery.epoch with
    | none => exact (no_returned_of_returnedAt_none _ _ hreturned ⟨request, signature, hentry, hepoch⟩).elim
    | some pair =>
        obtain ⟨hselected, hselectedEpoch⟩ := returned_of_returnedAt _ _ pair.1 pair.2 hreturned
        obtain ⟨hrequest, hsignature⟩ := SigningTranscript.returned_eq_of_same_leafIndex
          hevent.signingTranscript_valid hentry hselected (hepoch.trans hselectedEpoch.symm)
        refine ⟨pair.1, pair.2, rfl, ?_⟩
        rw [← hrequest, ← hsignature, ← hepoch]
        exact hcollision.2.symm
  · obtain ⟨_encoding, _hvalid, _hno, _hdecode, hfalse⟩ := hfresh
    exact hfalse.elim

theorem verificationPhase_run_fresh (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hfresh : cache (forgeryEncodingInput publicKey prefixResult.1) = none) :
    (simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run cache = (do
      let output ← ($ᵗ HashOutput)
      let result ← (simulateQ randomOracle (verifyAfterDigest publicKey prefixResult.1.epoch
        prefixResult.1.signature (truncateHash output))).run
          (cache.cacheQuery (forgeryEncodingInput publicKey prefixResult.1) output)
      pure (⟨publicKey, secretKey, prefixResult.1, prefixResult.2, result.1⟩, result.2)) := by
  unfold verificationPhase
  rw [simulateQ_bind, StateT.run_bind, verify_run_fresh _ _ _ _ _ hfresh, bind_assoc]
  rfl

theorem verificationPhase_fresh_encoding_probability_le (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hparameter : publicKey.parameter = secretKey.parameter)
    (hlog : SigningLogConsistent cache secretKey prefixResult.2)
    (hfresh : cache (forgeryEncodingInput publicKey prefixResult.1) = none) :
    Pr[fun result => WinningOutcomeBadEventOccurs result.2 result.1 .encoding |
      (simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run cache] ≤
        if HasAcceptedEncoding secretKey.parameter cache
          then ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ else 0 := by
  cases hreturned : returnedAt prefixResult.2 prefixResult.1.epoch with
  | none =>
      apply le_of_eq_of_le _ zero_le
      apply probEvent_eq_zero
      intro result hresult hevent
      obtain ⟨_hpk, _hsk, hforgery, hsigningLog, _⟩ := verificationPhase_support _ _ _ _ _ hresult
      obtain ⟨request, signature, htarget, _⟩ := winning_encoding_event_signed_target _ _ hevent
      rw [hsigningLog, hforgery, hreturned] at htarget
      cases htarget
  | some pair =>
      obtain ⟨hentry, _hepoch⟩ := returned_of_returnedAt _ _ pair.1 pair.2 hreturned
      obtain ⟨encoding, hdecode, _hsignature⟩ := hlog pair.1 pair.2 hentry
      have haccepted := hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode
      rw [if_pos haccepted, verificationPhase_run_fresh _ _ _ _ hfresh]
      let target := CacheView.encodingHash cache secretKey.parameter pair.1.epoch
        (pair.1.message, pair.2.randomness)
      calc
        _ ≤ Pr[fun output : HashOutput => truncateHash output = target | $ᵗ HashOutput] := by
          apply probEvent_bind_le_probEvent
          intro output _houtput hmiss
          simp only [bind_pure_comp, probEvent_map]
          apply probEvent_eq_zero
          intro result hresult hevent
          have hcacheLe := CacheReplay.randomOracle_cache_le _ _ result hresult
          have hinitialLe : cache ≤ result.2 := (QueryCache.le_cacheQuery cache hfresh).trans hcacheLe
          have hforged : result.2 (forgeryEncodingInput publicKey prefixResult.1) = some output :=
            hcacheLe (QueryCache.cacheQuery_self _ _ _)
          obtain ⟨request, signature, htarget, hhash⟩ := winning_encoding_event_signed_target _ _ hevent
          change returnedAt prefixResult.2 prefixResult.1.epoch = some (request, signature) at htarget
          rw [hreturned] at htarget
          cases htarget
          obtain ⟨signedOutput, hsigned⟩ := CacheView.encodingInput_cached_of_decode_some _ _ _ _ _ _ hdecode
          have hsignedHash := encodingHash_eq_of_cached cache result.2 hinitialLe secretKey.parameter
            request.epoch (request.message, signature.randomness) (by simp [hsigned])
          change CacheView.encodingHash result.2 secretKey.parameter prefixResult.1.epoch
              (prefixResult.1.message, prefixResult.1.signature.randomness) =
            CacheView.encodingHash result.2 secretKey.parameter request.epoch
              (request.message, signature.randomness) at hhash
          rw [← hsignedHash, ← hparameter] at hhash
          have hforgedHash : CacheView.encodingHash result.2 publicKey.parameter prefixResult.1.epoch
              (prefixResult.1.message, prefixResult.1.signature.randomness) = truncateHash output := by
            exact CacheView.digestAt_eq_of_cache_eq_some hforged
          rw [hforgedHash] at hhash
          apply hmiss
          simpa only [target, hparameter] using hhash
        _ = _ := Rom.uniform_truncate_probability target

/-- info: 'XmssSecurity.TargetSum.Deciding.verificationPhase_fresh_encoding_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPhase_fresh_encoding_probability_le

end XmssSecurity.TargetSum.Deciding

import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayCollision
import XmssSecurity.Proof.TargetSum.EUFCMA.SigningSuccess

/-! A single encoding probe selects a valid candidate, or falls back to a second
fresh message. Verification supplies the fallback encoding query. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Attack

noncomputable def replayFallbackExperiment (publicKey : PublicKey) (leafIndex : LeafIndex)
    (candidate fallback : Message) (signature : Signature) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let probe ← (randomOracle (CacheView.encodingInput publicKey.parameter leafIndex
    (candidate, signature.randomness))).run cache
  let message := if TargetSum.ValidDigest (truncateHash probe.1) then candidate else fallback
  let result ← (simulateQ randomOracle (verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool)).run probe.2
  return result.1

noncomputable def replayFallbackRate : ℝ≥0∞ :=
  replayCollisionRate + (1 - TargetSum.acceptanceProbability) * replayCollisionRate

theorem replayFallbackScore_average (target : Digest) :
    (∑' output, Pr[= output | $ᵗ HashOutput] *
      (replayScore target output +
        if ¬ TargetSum.ValidDigest (truncateHash output) then replayCollisionRate else 0)) =
      replayFallbackRate := by
  classical
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, replayScore_average]
  unfold replayFallbackRate
  congr 1
  rw [← TargetSum.probEvent_invalidDigest_uniformHashOutput, probEvent_eq_tsum_ite,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro output
  by_cases hvalid : TargetSum.ValidDigest (truncateHash output) <;> simp [hvalid]

theorem replayFallbackExperiment_lower
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (candidate fallback : Message) (hne : fallback ≠ candidate)
    (encoding : Encoding) (hvalid : TargetSum.Valid encoding) (randomness : Randomness)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hroot : RootCache keyResult.1.2.parameter leafIndex keyResult.1.1.root cache)
    (hcandidate : cache (CacheView.encodingInput keyResult.1.2.parameter leafIndex
      (candidate, randomness)) = none)
    (hfallback : cache (CacheView.encodingInput keyResult.1.2.parameter leafIndex
      (fallback, randomness)) = none) :
    replayFallbackRate ≤ Pr[= true | replayFallbackExperiment keyResult.1.1 leafIndex candidate fallback
      (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding) cache] := by
  classical
  have hparameter := Deciding.keygen_publicKey_parameter_eq keyResult hkey
  have htarget : TargetSum.ValidDigest (digestOfEncoding encoding) :=
    ⟨encoding, digestOfEncoding_decode encoding hvalid⟩
  unfold replayFallbackExperiment
  change replayFallbackRate ≤ Pr[= true | (randomOracle (CacheView.encodingInput keyResult.1.1.parameter
    leafIndex (candidate, randomness))).run cache >>= _]
  rw [hparameter, randomOracle_run_none_eq_uniformHashOutput _ _ hcandidate,
    uniformHashOutput, bind_map_left, ← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum,
    ← replayFallbackScore_average (digestOfEncoding encoding)]
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  by_cases haccepted : TargetSum.ValidDigest (truncateHash output)
  · simp only [haccepted, if_true, not_true_eq_false, if_false, add_zero]
    exact replayScore_le_cached_verification keyResult hkey leafIndex candidate encoding hvalid randomness
      cache hle hroot hcandidate output
  · have hmiss : truncateHash output ≠ digestOfEncoding encoding := fun heq => haccepted (heq ▸ htarget)
    simp only [replayScore, haccepted, hmiss, if_false, not_false_eq_true, if_true, zero_add]
    apply verify_fresh_replay_probability_ge keyResult hkey leafIndex fallback encoding hvalid randomness
    · exact hle.trans (QueryCache.le_cacheQuery cache hcandidate)
    · exact rootCache_cache_encoding _ _ _ _ hroot _ _ _ _
    · rw [QueryCache.cacheQuery_of_ne]
      · exact hfallback
      · intro heq
        exact hne (congrArg Prod.fst (CacheView.encodingInput_eq_iff _ _ _ _ _ |>.mp heq).2)

theorem encodingInput_fresh_after_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (answer : Option Signature) (signCache : QueryCache HashSpec)
    (hsign : (answer, signCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (message : Message) (hne : message ≠ request.message) (randomness : Randomness) :
    signCache (CacheView.encodingInput keyResult.1.2.parameter request.epoch (message, randomness)) = none := by
  rw [precomputedCappedSign] at hsign
  have hagree := precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit
    keyResult.1.2 request.epoch request.message
    (CacheView.encodingInput keyResult.1.2.parameter request.epoch (message, randomness)) (by
      intro signingRandomness heq
      have hpair := CacheView.encodingInput_injective keyResult.1.2.parameter request.epoch heq
      exact hne (congrArg Prod.fst hpair).symm)
    keyResult.2 signCache answer hsign
  rw [hagree]
  exact precomputedKeygen_cache_none_encodingInput keyResult hkey request.epoch _

noncomputable def signedReplayFallbackExperiment
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (request : SignRequest) (candidate fallback : Message) : ProbComp Bool := do
  let result ← (simulateQ romImpl
    (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  match result.1 with
  | none => pure false
  | some original => replayFallbackExperiment keyResult.1.1 request.epoch candidate fallback original result.2

theorem signedReplayFallbackExperiment_lower
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (candidate fallback : Message)
    (hcandidate : candidate ≠ request.message) (hfallback : fallback ≠ request.message)
    (hne : fallback ≠ candidate) :
    (131071 / 131072 : ℝ≥0∞) * replayFallbackRate ≤
      Pr[= true | signedReplayFallbackExperiment keyResult request candidate fallback] := by
  classical
  let signing := (simulateQ romImpl
    (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * replayFallbackRate :=
      mul_le_mul' (signing_success_gt_131071_over_131072 keyResult hkey request.epoch request.message).le le_rfl
    _ ≤ _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      unfold signedReplayFallbackExperiment
      rw [probOutput_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, signCache⟩
      by_cases hmem : (answer, signCache) ∈ support signing
      · cases answer with
        | none => simp
        | some original =>
            obtain ⟨encoding, hdecode, hreplay⟩ := signing_success_replay_at_keygen keyResult hkey
              request original signCache hmem
            simp only [ne_eq, Option.some_ne_none, not_false_eq_true, if_true]
            apply mul_le_mul' le_rfl
            rw [hreplay]
            apply replayFallbackExperiment_lower keyResult hkey request.epoch candidate fallback hne
              encoding (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2 original.randomness signCache
            · exact xmssRom_cache_le _ keyResult.2 (some original, signCache) hmem
            · exact rootCache_after_signing keyResult.1.2 request.epoch keyResult.1.1.root request
                (some original) keyResult.2 signCache (rootCache_after_keygen keyResult hkey request.epoch) hmem
            · exact encodingInput_fresh_after_signing keyResult hkey request
                (some original) signCache hmem candidate hcandidate original.randomness
            · exact encodingInput_fresh_after_signing keyResult hkey request
                (some original) signCache hmem fallback hfallback original.randomness
      · have hzero := probOutput_eq_zero_of_not_mem_support hmem
        change _ ≤ Pr[= (answer, signCache) | signing] * _
        rw [hzero]
        simp

theorem signedReplayFallbackRate_gt_127 :
    ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ < (131071 / 131072 : ℝ≥0∞) * replayFallbackRate := by
  unfold replayFallbackRate replayCollisionRate digestCollisionRate TargetSum.acceptanceProbability
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hp : (11539185377238682781344003244544752 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ 1 := by
    norm_num [digestBits, ENNReal.div_le_iff]
  rw [ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top]
  norm_num [digestBits, ENNReal.toReal_sub_of_le, ENNReal.toReal_inv, ENNReal.toReal_div]

end XmssSecurity.TargetSum.EUFCMA

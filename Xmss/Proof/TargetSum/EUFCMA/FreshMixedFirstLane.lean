import Xmss.Proof.TargetSum.EUFCMA.MixedPrefixProbe
import Xmss.Proof.TargetSum.EUFCMA.FreshFirstLaneBridge
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Preserve standard message freshness while combining the cached encoding and
the verifier's fresh encoding in one first-lane prefix experiment. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

attribute [local irreducible] Xmss.TargetSum.decodeDigest

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

def FreshMixedPrefixEvent (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedExecution.SourceExactTracedState) (fallback : Option Encoding) : Prop :=
  ¬ Unforgeability.SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1 ∧
    MixedEncodingPrefixEvent key result fallback

theorem freshMixedPrefixEvent_none (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedExecution.SourceExactTracedState) :
    FreshMixedPrefixEvent key result none ↔ FreshPrefixFirstLaneEvent key result := by
  have hdecode : (∃ encoding, Deciding.forgedEncoding result.2.1.1.1 key.secretKey.parameter
      result.1 = some encoding) ↔
      ∃ encoding, Code.decodeDigest (CacheView.encodingHash result.2.1.1.1
        key.secretKey.parameter result.1.epoch (result.1.message, result.1.signature.randomness)) =
          some encoding :=
    exists_congr fun _ => ⟨CacheView.decodeDigest_of_decodedEncoding,
      TargetSum.decodedEncoding_of_decodeDigest⟩
  simp only [FreshMixedPrefixEvent, MixedEncodingPrefixEvent, reduceCtorEq, false_and,
    exists_false, and_false, or_false, FreshPrefixFirstLaneEvent, AcceptedPrefixFirstLaneEvent,
    SourcePrefixFreshAccepted, Option.isSome_iff_exists]
  rw [hdecode]
  tauto

noncomputable def freshMixedPrefixProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun pair => FreshMixedPrefixEvent pair.1.1 pair.1.2
    (Code.decodeDigest (pair.2)) | mixedEncodingPrefixProgram adversary]

theorem sourcePrefixFinish_standardFresh (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Deciding.sourcePrefixExecution adversary key))
    (result : (Forgery × Bool) × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixFinish key prefixResult))
    (hwin : standardWon (CappedExecution.cappedBothEncodingProjection (CappedExecution.sourceGlobalExactProgramResult (key, result))).1 = true) :
    ¬ Unforgeability.SigningTranscript.ContainsRequest prefixResult.2.2.toSigningLog prefixResult.1 := by
  have hlogs := CappedExecution.cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [Deciding.sourcePrefixFinish, support_map] at hresult
  obtain ⟨verified, _, rfl⟩ := hresult
  have hfresh := ((standardWon_eq_true_iff _).mp hwin).2.1
  simpa only [CappedExecution.cappedBothEncodingProjection, CappedExecution.sourceGlobalExactProgramResult,
    CappedExecution.sourceGlobalExactExecutionResult, hlogs] using hfresh

theorem sourcePrefixFinish_freshFirstLane_probability_le_mixed_add_encoding (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Deciding.sourcePrefixExecution adversary key)) :
    Pr[fun result => SourceWinningFreshFirstLane (key, result) | Deciding.sourcePrefixFinish key prefixResult] ≤
      Pr[fun output => FreshMixedPrefixEvent key prefixResult
        (Code.decodeDigest (output)) | $ᵗ Digest] +
      Pr[fun result => SourcePrefixForgedEncodingFresh (key, prefixResult) ∧
        SourceWinningEncodingEvent (key, result) | Deciding.sourcePrefixFinish key prefixResult] := by
  by_cases hfresh : ¬ Unforgeability.SigningTranscript.ContainsRequest prefixResult.2.2.toSigningLog prefixResult.1
  · simp only [FreshMixedPrefixEvent, hfresh, not_false_eq_true, true_and]
    apply le_trans _ (sourcePrefixFinish_firstLane_probability_le_mixed_add_encoding adversary key hkey prefixResult hprefix)
    exact probEvent_mono'' (fun _ hevent => hevent.2)
  · have hzero : Pr[fun result => SourceWinningFreshFirstLane (key, result) |
        Deciding.sourcePrefixFinish key prefixResult] = 0 := by
      apply probEvent_eq_zero
      intro result hresult hevent
      exact hfresh (sourcePrefixFinish_standardFresh adversary key prefixResult hprefix result hresult hevent.1)
    rw [hzero]
    exact zero_le

theorem freshMixedPrefixProbability_eq_prefix (adversary : Adversary) :
    freshMixedPrefixProbability adversary =
      Pr[fun pair : MixedEncodingPrefixResult => FreshMixedPrefixEvent pair.1.1 pair.1.2
        (Code.decodeDigest (pair.2)) | do
          let prefixPair ← Deciding.sourcePrefixProgram adversary
          let output ← ($ᵗ Digest)
          pure (prefixPair, output)] := by
  unfold freshMixedPrefixProbability mixedEncodingPrefixProgram
  apply CappedExecution.probEvent_eq_of_evalDist_eq
  exact OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ Digest) (Deciding.sourcePrefixProgram adversary)
    (fun output prefixPair => pure (prefixPair, output))

theorem freshFirstLane_probability_le_mixed_add_encoding (adversary : Adversary) :
    Pr[WinningFreshFirstLane | cappedDetailedGameWithEncodingTrace adversary] ≤
      freshMixedPrefixProbability adversary + freshSourceEncodingProbability adversary := by
  rw [freshFirstLane_probability_eq_source, Deciding.sourceProgram_eq_prefix_finish,
    freshMixedPrefixProbability_eq_prefix]
  unfold freshSourceEncodingProbability
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro pair
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  rw [← mul_add]
  by_cases hpair : pair ∈ support (Deciding.sourcePrefixProgram adversary)
  · apply mul_le_mul' le_rfl
    unfold Deciding.sourcePrefixProgram at hpair
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
    obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
    exact sourcePrefixFinish_freshFirstLane_probability_le_mixed_add_encoding adversary key hkey prefixResult hprefix
  · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]

/-- info: 'Xmss.TargetSum.EUFCMA.freshFirstLane_probability_le_mixed_add_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshFirstLane_probability_le_mixed_add_encoding

end Xmss.TargetSum.EUFCMA

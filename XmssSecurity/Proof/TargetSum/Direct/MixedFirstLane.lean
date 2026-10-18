import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbability
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Transfer the actual first-lane event into the joint cached-or-fresh prefix
experiment. Only the separately paid fresh encoding collision remains outside it. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain Direct FirstLaneOracleSimulation

theorem sourcePrefix_forgedEncoding_eq_none_of_fresh
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Generic.Deciding.forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1 = none := by
  have hparameter := Generic.CappedChain.keygen_parameter_eq key.keyResult
    (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  change key.publicKey.parameter = key.secretKey.parameter at hparameter
  change prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.publicKey.parameter prefixResult.1.epoch
    (prefixResult.1.message, prefixResult.1.signature.randomness)) = none at hfresh
  rw [hparameter] at hfresh
  simp only [Generic.Deciding.forgedEncoding, Generic.Concrete.CacheView.decodedEncoding, hfresh]

theorem sourcePrefixFinish_fresh_revealed_probability_le_mixed (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Generic.Deciding.sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) | Generic.Deciding.sourcePrefixFinish key prefixResult] ≤
      Pr[fun output => MixedEncodingPrefixEvent key prefixResult
        (Generic.Code.decodeDigest (Generic.truncateHash output)) | $ᵗ HashOutput] := by
  rw [sourcePrefixFinish_eq_uniform_afterHash _ _ hfresh]
  apply probEvent_bind_le_probEvent
  intro output _ hnone
  by_cases hvalid : Generic.Code.ValidDigest (Generic.truncateHash output)
  · apply probEvent_eq_zero
    intro result hresult hevent
    let accepted : TargetSum.AcceptedHashOutput := ⟨output, hvalid⟩
    apply hnone
    refine Or.inr ⟨sourcePrefix_forgedEncoding_eq_none_of_fresh key hkey prefixResult hfresh,
      TargetSum.acceptedHashEncoding accepted, TargetSum.acceptedHashEncoding_decode accepted, ?_⟩
    exact sourcePrefixFinishAfterHash_revealed_implies_prefixEvent adversary key hkey prefixResult hprefix
      accepted hfresh result hresult hevent
  · exact sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid key prefixResult output hvalid

theorem sourcePrefixFinish_firstLane_probability_le_mixed_add_encoding (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Generic.Deciding.sourcePrefixExecution adversary key)) :
    Pr[fun result => Generic.Deciding.SourceWinningDecidingFirstLaneEvent (key, result) | Generic.Deciding.sourcePrefixFinish key prefixResult] ≤
      Pr[fun output => MixedEncodingPrefixEvent key prefixResult
        (Generic.Code.decodeDigest (Generic.truncateHash output)) | $ᵗ HashOutput] +
      Pr[fun result => SourcePrefixForgedEncodingFresh (key, prefixResult) ∧
        SourceWinningEncodingEvent (key, result) | Generic.Deciding.sourcePrefixFinish key prefixResult] := by
  by_cases hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)
  · simp only [hfresh, true_and]
    have hsplit : Pr[fun result => Generic.Deciding.SourceWinningDecidingFirstLaneEvent (key, result) |
        Generic.Deciding.sourcePrefixFinish key prefixResult] ≤
        Pr[fun result => SourceWinningRevealedEvent (key, result) | Generic.Deciding.sourcePrefixFinish key prefixResult] +
        Pr[fun result => SourceWinningEncodingEvent (key, result) | Generic.Deciding.sourcePrefixFinish key prefixResult] := by
      apply le_trans _ (probEvent_or_le _ _ _)
      apply probEvent_mono''
      intro result hevent
      rcases hevent with hencoding | hrevealed
      · exact Or.inr hencoding.1
      · exact Or.inl hrevealed
    exact hsplit.trans (add_le_add
      (sourcePrefixFinish_fresh_revealed_probability_le_mixed adversary key hkey prefixResult hprefix hfresh) le_rfl)
  · simp only [hfresh, false_and, probEvent_False, add_zero]
    by_cases haccepted : AcceptedPrefixFirstLaneEvent key prefixResult
    · have htrue : Pr[fun output => MixedEncodingPrefixEvent key prefixResult
          (Generic.Code.decodeDigest (Generic.truncateHash output)) | $ᵗ HashOutput] = 1 := by
        simp [MixedEncodingPrefixEvent, haccepted]
      rw [htrue]
      exact probEvent_le_one
    · have hzero : Pr[fun result => Generic.Deciding.SourceWinningDecidingFirstLaneEvent (key, result) |
          Generic.Deciding.sourcePrefixFinish key prefixResult] = 0 := by
        apply probEvent_eq_zero
        intro result hresult hevent
        apply haccepted
        apply sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix _ result hresult hevent
        have hparameter := Generic.CappedChain.keygen_parameter_eq key.keyResult
          (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
        change key.publicKey.parameter = key.secretKey.parameter at hparameter
        change prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.publicKey.parameter prefixResult.1.epoch
          (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none at hfresh
        rw [hparameter] at hfresh
        exact hfresh
      rw [hzero]
      exact zero_le

theorem mixedEncodingPrefixProbability_eq_prefix (adversary : Generic.Adversary) :
    mixedEncodingPrefixProbability adversary =
      Pr[fun pair : MixedEncodingPrefixResult => MixedEncodingPrefixEvent pair.1.1 pair.1.2
        (Generic.Code.decodeDigest (Generic.truncateHash pair.2)) | do
          let prefixPair ← Generic.Deciding.sourcePrefixProgram adversary
          let output ← ($ᵗ HashOutput)
          pure (prefixPair, output)] := by
  unfold mixedEncodingPrefixProbability mixedEncodingPrefixProgram
  apply Generic.CappedChain.probEvent_eq_of_evalDist_eq
  exact OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ HashOutput) (Generic.Deciding.sourcePrefixProgram adversary)
    (fun output prefixPair => pure (prefixPair, output))

theorem decidingFirstLane_probability_le_mixed_add_encoding (adversary : Generic.Adversary) :
    Pr[Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] ≤
      mixedEncodingPrefixProbability adversary + freshSourceEncodingProbability adversary := by
  rw [Generic.Deciding.decidingFirstLane_probability_eq_source, Generic.Deciding.sourceProgram_eq_prefix_finish,
    mixedEncodingPrefixProbability_eq_prefix]
  unfold freshSourceEncodingProbability
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro pair
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  rw [← mul_add]
  by_cases hpair : pair ∈ support (Generic.Deciding.sourcePrefixProgram adversary)
  · apply mul_le_mul' le_rfl
    unfold Generic.Deciding.sourcePrefixProgram at hpair
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
    obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
    exact sourcePrefixFinish_firstLane_probability_le_mixed_add_encoding adversary key hkey prefixResult hprefix
  · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]

theorem decidingFirstLane_probability_le_shared_prefix (adversary : Generic.Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Generic.Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[Generic.Deciding.WinningDecidingFirstLaneBadEventOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (2 * (Generic.Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) + 1)) /
            ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (decidingFirstLane_probability_le_mixed_add_encoding adversary).trans
  apply (add_le_add (mixedEncodingPrefixProbability_le adversary limit hbudget)
    (freshSourceEncodingProbability_le_source_credit adversary)).trans_eq
  simp only [div_eq_mul_inv]
  ring

/-- info: 'XmssSecurity.TargetSum.Deciding.decidingFirstLane_probability_le_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_shared_prefix

end XmssSecurity.TargetSum.Deciding

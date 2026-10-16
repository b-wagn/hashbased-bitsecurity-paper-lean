import XmssSecurity.Proof.Direct.FreshFirstLaneContribution
import XmssSecurity.Proof.Direct.FreshEncodingCollisionBudget

/-! Split the fresh first lane into an encoding collision and a revealed deciding
value. The encoding collision is paid by the source's acceptance credit. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain Direct

def SourceWinningEncodingEvent (result : SourceGlobalExactTracedProgramResult) : Prop :=
  let execution := cappedBothEncodingProjection (sourceGlobalExactProgramResult result)
  WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding

def SourceWinningRevealedEvent (result : SourceGlobalExactTracedProgramResult) : Prop :=
  let execution := cappedBothEncodingProjection (sourceGlobalExactProgramResult result)
  execution.1.won = true ∧ DecidingChainValueRevealed execution.2.1.1 execution.1

noncomputable def freshSourceEncodingProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => SourcePrefixForgedEncodingFresh result.1 ∧
      SourceWinningEncodingEvent (result.1.1, result.2) | do
    let prefixPair ← sourcePrefixProgram adversary
    let result ← sourcePrefixFinish prefixPair.1 prefixPair.2
    pure (prefixPair, result)]

noncomputable def freshRevealedProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => SourcePrefixForgedEncodingFresh result.1 ∧
      SourceWinningRevealedEvent (result.1.1, result.2) | do
    let prefixPair ← sourcePrefixProgram adversary
    let result ← sourcePrefixFinish prefixPair.1 prefixPair.2
    pure (prefixPair, result)]

theorem sourcePrefixFinish_fresh_encoding_probability_le (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Pr[fun result => SourceWinningEncodingEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      if HasAcceptedEncoding key.secretKey.parameter prefixResult.2.1.1.1
        then ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ else 0 := by
  have hkeygen := Concrete.oldKeygen_support_materializedPrecomputedKeygen key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have hphase := sourcePrefixExecution_phase_support adversary key prefixResult hprefix
  have hlog := adversaryPhase_signingLog_consistent adversary
    (Concrete.materializeCachedKeyResult key.keyResult) hkeygen
    ((prefixResult.1, prefixResult.2.2.toSigningLog), prefixResult.2.1.1.1) hphase
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [← hlogs] at hlog
  have h := verificationPhase_fresh_encoding_probability_le key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey)
    (prefixResult.1, prefixResult.2.1.1.2.toSigningLog) prefixResult.2.1.1.1
    (keygen_publicKey_parameter_eq _ hkeygen) hlog hfresh
  unfold verificationPhase at h
  rw [simulateQ_bind, StateT.run_bind] at h
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, probEvent_map] at h
  rw [sourcePrefixFinish, probEvent_map]
  exact h

theorem sourcePrefix_accepted_probability_le (adversary : Adversary) :
    Pr[fun result => HasAcceptedEncoding result.1.secretKey.parameter result.2.2.1.1.1 |
      sourcePrefixProgram adversary] ≤
        Checksum.acceptanceProbability *
          (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  exact sourceCountedPrefix_accepted_probability_le adversary

theorem freshSourceEncodingProbability_le_source_credit (adversary : Adversary) :
    freshSourceEncodingProbability adversary ≤
      (Checksum.acceptanceProbability *
        (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary)) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let rate := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  unfold freshSourceEncodingProbability
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' pair, Pr[= pair | sourcePrefixProgram adversary] *
        (if HasAcceptedEncoding pair.1.secretKey.parameter pair.2.2.1.1.1 then rate else 0) := by
      apply ENNReal.tsum_le_tsum
      intro pair
      by_cases hpair : pair ∈ support (sourcePrefixProgram adversary)
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        by_cases hfresh : SourcePrefixForgedEncodingFresh pair
        · simp only [hfresh, true_and]
          unfold sourcePrefixProgram at hpair
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
          obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
          exact sourcePrefixFinish_fresh_encoding_probability_le adversary key hkey prefixResult hprefix hfresh
        · simp only [hfresh, false_and, probEvent_False]
          exact zero_le
      · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]
    _ = Pr[fun result => HasAcceptedEncoding result.1.secretKey.parameter result.2.2.1.1.1 |
        sourcePrefixProgram adversary] * rate := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro pair
      split_ifs <;> simp only [mul_zero, zero_mul]
    _ ≤ _ := by
      simpa only [rate, div_eq_mul_inv] using
        mul_le_mul' (sourcePrefix_accepted_probability_le adversary) (le_refl rate)

theorem freshFirstLaneProbability_le_encoding_add_revealed (adversary : Adversary) :
    freshFirstLaneProbability adversary ≤
      freshSourceEncodingProbability adversary + freshRevealedProbability adversary := by
  unfold freshFirstLaneProbability freshSourceEncodingProbability freshRevealedProbability
  apply le_trans _ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result _ hevent
  rcases hevent.2 with hencoding | hrevealed
  · exact Or.inl ⟨hevent.1, hencoding.1⟩
  · exact Or.inr ⟨hevent.1, hrevealed⟩

theorem freshFirstLaneProbability_le_source_credit_add_revealed (adversary : Adversary) :
    freshFirstLaneProbability adversary ≤
      (Checksum.acceptanceProbability *
        (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary)) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) + freshRevealedProbability adversary :=
  (freshFirstLaneProbability_le_encoding_add_revealed adversary).trans
    (add_le_add (freshSourceEncodingProbability_le_source_credit adversary) le_rfl)

/-- info: 'XmssSecurity.Deciding.freshFirstLaneProbability_le_source_credit_add_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshFirstLaneProbability_le_source_credit_add_revealed

end XmssSecurity.Deciding

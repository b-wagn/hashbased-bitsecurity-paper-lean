import XmssSecurity.Proof.AcceptedHashSampling
import XmssSecurity.Proof.Direct.FreshFirstLaneSplit

/-! A fresh revealed-value event factors into the ordinary encoding acceptance rate
and an experiment that samples the final hash only from accepted outputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open Concrete CappedChain Direct

noncomputable def sourcePrefixFinishAfterHash (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState) (output : HashOutput) :
    ProbComp ((Forgery × Bool) × SourceExactTracedState) :=
  (fun verified : Bool × QueryCache HashSpec =>
    ((prefixResult.1, verified.1),
      (((verified.2, prefixResult.2.1.1.2),
        appendVerificationEncodingObservation (materializePrecomputation key.cache key.secretKey)
          prefixResult.1 prefixResult.2.1.1.1 verified.2 prefixResult.2.1.2), prefixResult.2.2))) <$>
      (simulateQ randomOracle (verifyAfterDigest key.publicKey prefixResult.1.epoch
        prefixResult.1.signature (truncateHash output))).run
          (prefixResult.2.1.1.1.cacheQuery (forgeryEncodingInput key.publicKey prefixResult.1) output)

theorem sourcePrefixFinish_eq_uniform_afterHash (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    sourcePrefixFinish key prefixResult =
      ($ᵗ HashOutput) >>= sourcePrefixFinishAfterHash key prefixResult := by
  unfold sourcePrefixFinish sourcePrefixFinishAfterHash
  rw [verify_run_fresh _ _ _ _ _ hfresh, map_bind]

theorem sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid
    (key : ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × SourceExactTracedState)
    (output : HashOutput) (hinvalid : ¬Checksum.ValidDigest (truncateHash output)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) |
      sourcePrefixFinishAfterHash key prefixResult output] = 0 := by
  unfold sourcePrefixFinishAfterHash
  rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp [SourceWinningRevealedEvent, cappedBothEncodingProjection, sourceGlobalExactProgramResult,
    sourceGlobalExactExecutionResult, GameOutcome.won]

theorem sourcePrefixFinish_fresh_revealed_probability_eq_acceptance_mul
    (key : ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) | sourcePrefixFinish key prefixResult] =
      Checksum.acceptanceProbability * Pr[fun result => SourceWinningRevealedEvent (key, result) |
        ($ᵗ Checksum.AcceptedHashOutput) >>= fun output => sourcePrefixFinishAfterHash key prefixResult output.1] := by
  rw [sourcePrefixFinish_eq_uniform_afterHash _ _ hfresh]
  exact Checksum.uniformHashOutput_bind_probability_eq_acceptance_mul _ _
    (sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid key prefixResult)

noncomputable def acceptedFreshRevealedProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => SourcePrefixForgedEncodingFresh result.1 ∧
      SourceWinningRevealedEvent (result.1.1, result.2) | do
    let prefixPair ← sourcePrefixProgram adversary
    let output ← ($ᵗ Checksum.AcceptedHashOutput)
    let result ← sourcePrefixFinishAfterHash prefixPair.1 prefixPair.2 output.1
    pure (prefixPair, result)]

theorem freshRevealedProbability_eq_acceptance_mul (adversary : Adversary) :
    freshRevealedProbability adversary =
      Checksum.acceptanceProbability * acceptedFreshRevealedProbability adversary := by
  classical
  unfold freshRevealedProbability acceptedFreshRevealedProbability
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro prefixPair
  rw [← bind_assoc]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  by_cases hfresh : SourcePrefixForgedEncodingFresh prefixPair
  · simp only [hfresh, true_and]
    rw [sourcePrefixFinish_fresh_revealed_probability_eq_acceptance_mul _ _ hfresh, mul_left_comm]
  · simp only [hfresh, false_and, probEvent_False, mul_zero]

/-- info: 'XmssSecurity.Deciding.freshRevealedProbability_eq_acceptance_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshRevealedProbability_eq_acceptance_mul

end XmssSecurity.Deciding

import XmssSecurity.Proof.TargetSum.AcceptedHashSampling
import XmssSecurity.Proof.TargetSum.Direct.FreshFirstLaneSplit

/-! A fresh revealed-value event factors into the ordinary encoding acceptance rate
and an experiment that samples the final hash only from accepted outputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

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
    (output : HashOutput) (hinvalid : ¬TargetSum.ValidDigest (truncateHash output)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) |
      sourcePrefixFinishAfterHash key prefixResult output] = 0 := by
  unfold sourcePrefixFinishAfterHash
  rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp [SourceWinningRevealedEvent, cappedBothEncodingProjection, sourceGlobalExactProgramResult,
    sourceGlobalExactExecutionResult, GameOutcome.won]

end XmssSecurity.TargetSum.Deciding

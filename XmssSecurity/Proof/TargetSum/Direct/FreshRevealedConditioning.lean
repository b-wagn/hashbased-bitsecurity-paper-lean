import XmssSecurity.Proof.TargetSum.AcceptedHashSampling
import XmssSecurity.Proof.TargetSum.Direct.FreshFirstLaneSplit
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A fresh revealed-value event factors into the ordinary encoding acceptance rate
and an experiment that samples the final hash only from accepted outputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain Direct

noncomputable def sourcePrefixFinishAfterHash (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState) (output : HashOutput) :
    ProbComp ((Generic.Forgery × Bool) × Generic.CappedChain.SourceExactTracedState) :=
  (fun verified : Bool × QueryCache HashSpec =>
    ((prefixResult.1, verified.1),
      (((verified.2, prefixResult.2.1.1.2),
        Generic.appendVerificationEncodingObservation (Generic.Concrete.materializePrecomputation key.cache key.secretKey)
          prefixResult.1 prefixResult.2.1.1.1 verified.2 prefixResult.2.1.2), prefixResult.2.2))) <$>
      (simulateQ randomOracle (Generic.Direct.verifyAfterDigest key.publicKey prefixResult.1.epoch
        prefixResult.1.signature (Generic.truncateHash output))).run
          (prefixResult.2.1.1.1.cacheQuery (Generic.Direct.forgeryEncodingInput key.publicKey prefixResult.1) output)

theorem sourcePrefixFinish_eq_uniform_afterHash (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Generic.Deciding.sourcePrefixFinish key prefixResult =
      ($ᵗ HashOutput) >>= sourcePrefixFinishAfterHash key prefixResult := by
  unfold Generic.Deciding.sourcePrefixFinish sourcePrefixFinishAfterHash
  rw [verify_run_fresh _ _ _ _ _ hfresh, map_bind]

theorem sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (output : HashOutput) (hinvalid : ¬Generic.Code.ValidDigest (Generic.truncateHash output)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) |
      sourcePrefixFinishAfterHash key prefixResult output] = 0 := by
  unfold sourcePrefixFinishAfterHash
  rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp [SourceWinningRevealedEvent, Generic.CappedChain.cappedBothEncodingProjection, Generic.CappedChain.sourceGlobalExactProgramResult,
    Generic.CappedChain.sourceGlobalExactExecutionResult, Generic.GameOutcome.won]

end XmssSecurity.TargetSum.Deciding

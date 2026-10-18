import XmssSecurity.Proof.TargetSum.AcceptedHashSampling
import XmssSecurity.Proof.TargetSum.Direct.FreshFirstLaneSplit
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A fresh revealed-value event factors into the ordinary encoding acceptance rate
and an experiment that samples the final hash only from accepted outputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain Direct

noncomputable def sourcePrefixFinishAfterHash (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × CappedChain.SourceExactTracedState) (output : Digest) :
    ProbComp ((Forgery × Bool) × CappedChain.SourceExactTracedState) :=
  (fun verified : Bool × QueryCache HashSpec =>
    ((prefixResult.1, verified.1),
      (((verified.2, prefixResult.2.1.1.2),
        appendVerificationEncodingObservation (Concrete.materializePrecomputation key.cache key.secretKey)
          prefixResult.1 prefixResult.2.1.1.1 verified.2 prefixResult.2.1.2), prefixResult.2.2))) <$>
      (simulateQ randomOracle (Direct.verifyAfterDigest key.publicKey prefixResult.1.epoch
        prefixResult.1.signature (output))).run
          (prefixResult.2.1.1.1.cacheQuery (Direct.forgeryEncodingInput key.publicKey prefixResult.1) output)

theorem sourcePrefixFinish_eq_uniform_afterHash (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × CappedChain.SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Deciding.sourcePrefixFinish key prefixResult =
      ($ᵗ Digest) >>= sourcePrefixFinishAfterHash key prefixResult := by
  unfold Deciding.sourcePrefixFinish sourcePrefixFinishAfterHash
  rw [verify_run_fresh _ _ _ _ _ hfresh, map_bind]

theorem sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × CappedChain.SourceExactTracedState)
    (output : Digest) (hinvalid : ¬Code.ValidDigest (output)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) |
      sourcePrefixFinishAfterHash key prefixResult output] = 0 := by
  unfold sourcePrefixFinishAfterHash
  rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp [SourceWinningRevealedEvent, CappedChain.cappedBothEncodingProjection, CappedChain.sourceGlobalExactProgramResult,
    CappedChain.sourceGlobalExactExecutionResult, GameOutcome.won]

end XmssSecurity.TargetSum.Deciding

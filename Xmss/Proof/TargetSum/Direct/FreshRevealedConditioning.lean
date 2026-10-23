import Xmss.Proof.TargetSum.AcceptedHashSampling
import Xmss.Proof.TargetSum.Direct.FreshFirstLaneSplit
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A fresh revealed-value event factors into the ordinary encoding acceptance rate
and an experiment that samples the final hash only from accepted outputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Direct

noncomputable def sourcePrefixFinishAfterHash (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState) (output : Digest) :
    ProbComp ((Forgery × Bool) × CappedExecution.SourceExactTracedState) :=
  (fun verified : Bool × QueryCache HashSpec =>
    ((prefixResult.1, verified.1),
      (((verified.2, prefixResult.2.1.1.2),
        appendVerificationEncodingObservation (Keygen.materializePrecomputation key.cache key.secretKey)
          prefixResult.1 prefixResult.2.1.1.1 verified.2 prefixResult.2.1.2), prefixResult.2.2))) <$>
      (simulateQ randomOracle (Direct.verifyAfterDigest key.publicKey prefixResult.1.epoch
        prefixResult.1.signature (output))).run
          (prefixResult.2.1.1.1.cacheQuery (Direct.forgeryEncodingInput key.publicKey prefixResult.1) output)

theorem sourcePrefixFinish_eq_uniform_afterHash (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Deciding.sourcePrefixFinish key prefixResult =
      ($ᵗ Digest) >>= sourcePrefixFinishAfterHash key prefixResult := by
  unfold Deciding.sourcePrefixFinish sourcePrefixFinishAfterHash
  rw [verify_run_fresh _ _ _ _ _ hfresh, map_bind]

theorem sourcePrefixFinishAfterHash_revealed_probability_eq_zero_of_invalid
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (output : Digest) (hinvalid : ¬Code.ValidDigest (output)) :
    Pr[fun result => SourceWinningRevealedEvent (key, result) |
      sourcePrefixFinishAfterHash key prefixResult output] = 0 := by
  unfold sourcePrefixFinishAfterHash
  rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp [SourceWinningRevealedEvent, CappedExecution.cappedBothEncodingProjection, CappedExecution.sourceGlobalExactProgramResult,
    CappedExecution.sourceGlobalExactExecutionResult, GameOutcome.won]

end Xmss.TargetSum.Deciding

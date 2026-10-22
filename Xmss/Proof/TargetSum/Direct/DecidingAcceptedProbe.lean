import Xmss.Proof.TargetSum.Direct.DecidingFirstLaneExpected
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Append the deciding probe only when the forged encoding is accepted. Winning first-lane
executions satisfy that condition, so rejected encodings incur no additional probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open Hashing Wots Merkle Verify Keygen Signing CappedExecution FirstLaneOracleSimulation

def AcceptedPrefixFirstLaneEvent (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedExecution.SourceExactTracedState) : Prop :=
  Deciding.PrefixFirstLaneEvent key result ∧
    (Deciding.forgedEncoding result.2.1.1.1 key.secretKey.parameter result.1).isSome

theorem sourceFinish_firstLane_forgedEncoding_some
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × CappedExecution.SourceExactTracedState)
    (hfinish : execution ∈ support (Deciding.sourcePrefixFinish key prefixResult))
    (hevent : Deciding.SourceWinningDecidingFirstLaneEvent (key, execution)) :
    (Deciding.forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1).isSome := by
  rw [Deciding.sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  rw [Deciding.forgedEncoding_eq_of_cache_le _ verified.2 (xmssRom_cache_le _ _ _ hverified)
    key.secretKey.parameter prefixResult.1 hcached]
  rcases hevent with hencoding | ⟨_hwin, hrevealed⟩
  · obtain ⟨encoding, hdecode⟩ := hencoding.1.forgery_decode
    change Deciding.forgedEncoding verified.2
      (materializePrecomputation key.cache key.secretKey).parameter prefixResult.1 = some encoding at hdecode
    rw [materializePrecomputation_parameter] at hdecode
    simp [hdecode]
  · obtain ⟨encoding, hdecode, _⟩ := hrevealed
    change Deciding.forgedEncoding verified.2
      (materializePrecomputation key.cache key.secretKey).parameter prefixResult.1 = some encoding at hdecode
    rw [materializePrecomputation_parameter] at hdecode
    simp [hdecode]

theorem sourceFirstLaneEvent_implies_acceptedPrefixEvent (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × CappedExecution.SourceExactTracedState)
    (hfinish : execution ∈ support (Deciding.sourcePrefixFinish key prefixResult))
    (hevent : Deciding.SourceWinningDecidingFirstLaneEvent (key, execution)) :
    AcceptedPrefixFirstLaneEvent key prefixResult :=
  ⟨Deciding.sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix hcached
      execution hfinish hevent,
    sourceFinish_firstLane_forgedEncoding_some key prefixResult hcached execution hfinish hevent⟩

theorem forgedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (CappedExecution.GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (forgery : Forgery) :
    Deciding.forgedEncoding leftCache parameter forgery = Deciding.forgedEncoding rightCache parameter forgery := by
  unfold Deciding.forgedEncoding
  rw [Deciding.decodedEncoding_eq_of_comparableCaches _ _ _ hcaches]

end Xmss.TargetSum.Deciding

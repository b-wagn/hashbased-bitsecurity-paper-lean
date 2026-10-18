import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneExpected
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Append the deciding probe only when the forged encoding is accepted. Winning first-lane
executions satisfy that condition, so rejected encodings incur no additional probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open Concrete Generic.CappedChain FirstLaneOracleSimulation

def AcceptedPrefixFirstLaneEvent (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (result : Generic.Forgery × Generic.CappedChain.SourceExactTracedState) : Prop :=
  Generic.Deciding.PrefixFirstLaneEvent key result ∧
    (Generic.Deciding.forgedEncoding result.2.1.1.1 key.secretKey.parameter result.1).isSome

theorem sourceFinish_firstLane_forgedEncoding_some
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hcached : prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Generic.Forgery × Bool) × Generic.CappedChain.SourceExactTracedState)
    (hfinish : execution ∈ support (Generic.Deciding.sourcePrefixFinish key prefixResult))
    (hevent : Generic.Deciding.SourceWinningDecidingFirstLaneEvent (key, execution)) :
    (Generic.Deciding.forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1).isSome := by
  rw [Generic.Deciding.sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  rw [Generic.Deciding.forgedEncoding_eq_of_cache_le _ verified.2 (Generic.xmssRom_cache_le _ _ _ hverified)
    key.secretKey.parameter prefixResult.1 hcached]
  rcases hevent with hencoding | ⟨_hwin, hrevealed⟩
  · obtain ⟨encoding, hdecode⟩ := hencoding.1.forgery_decode
    change Generic.Deciding.forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]
  · obtain ⟨encoding, hdecode, _⟩ := hrevealed
    change Generic.Deciding.forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]

theorem sourceFirstLaneEvent_implies_acceptedPrefixEvent (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Generic.Forgery × Generic.CappedChain.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Generic.Deciding.sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Generic.Forgery × Bool) × Generic.CappedChain.SourceExactTracedState)
    (hfinish : execution ∈ support (Generic.Deciding.sourcePrefixFinish key prefixResult))
    (hevent : Generic.Deciding.SourceWinningDecidingFirstLaneEvent (key, execution)) :
    AcceptedPrefixFirstLaneEvent key prefixResult :=
  ⟨Generic.Deciding.sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix hcached
      execution hfinish hevent,
    sourceFinish_firstLane_forgedEncoding_some key prefixResult hcached execution hfinish hevent⟩

theorem forgedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : Generic.HashCachesAgreeOn (Generic.CappedChain.GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (forgery : Generic.Forgery) :
    Generic.Deciding.forgedEncoding leftCache parameter forgery = Generic.Deciding.forgedEncoding rightCache parameter forgery := by
  unfold Generic.Deciding.forgedEncoding
  rw [Generic.Deciding.decodedEncoding_eq_of_comparableCaches _ _ _ hcaches]

end XmssSecurity.TargetSum.Deciding

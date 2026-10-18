import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneExpected

/-! Append the deciding probe only when the forged encoding is accepted. Winning first-lane
executions satisfy that condition, so rejected encodings incur no additional probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain FirstLaneOracleSimulation

def AcceptedPrefixFirstLaneEvent (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) : Prop :=
  PrefixFirstLaneEvent key result ∧
    (forgedEncoding result.2.1.1.1 key.secretKey.parameter result.1).isSome

theorem sourceFinish_firstLane_forgedEncoding_some
    (key : ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × SourceExactTracedState)
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningDecidingFirstLaneEvent (key, execution)) :
    (forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1).isSome := by
  rw [sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  rw [forgedEncoding_eq_of_cache_le _ verified.2 (xmssRom_cache_le _ _ _ hverified)
    key.secretKey.parameter prefixResult.1 hcached]
  rcases hevent with hencoding | ⟨_hwin, hrevealed⟩
  · obtain ⟨encoding, hdecode⟩ := hencoding.1.forgery_decode
    change forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]
  · obtain ⟨encoding, hdecode, _⟩ := hrevealed
    change forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]

theorem sourceFirstLaneEvent_implies_acceptedPrefixEvent (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningDecidingFirstLaneEvent (key, execution)) :
    AcceptedPrefixFirstLaneEvent key prefixResult :=
  ⟨sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix hcached
      execution hfinish hevent,
    sourceFinish_firstLane_forgedEncoding_some key prefixResult hcached execution hfinish hevent⟩

theorem forgedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (forgery : Forgery) :
    forgedEncoding leftCache parameter forgery = forgedEncoding rightCache parameter forgery := by
  unfold forgedEncoding
  rw [encodingHash_eq_of_comparableCaches _ _ _ hcaches]

end XmssSecurity.TargetSum.Deciding

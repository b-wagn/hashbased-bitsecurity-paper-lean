import XmssSecurity.Proof.EUFCMA.FreshEncoding
import XmssSecurity.Proof.Direct.DecidingPrefixProjection
import XmssSecurity.Proof.Direct.CountedSourceEncodingBudget

/-! A cached standard-fresh forgery witnesses a direct encoding query in the
existing source-prefix trace. Free signing cannot supply that witness. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem sourcePrefix_fresh_encoding_unqueried (adversary : XmssSecurity.Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixExecution adversary key))
    (hfresh : ¬ SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hunqueried : CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness) ∉ result.2.2.hashInputs) :
    result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) = none := by
  have hprojection : (result.1, (result.2.1.1.1, result.2.2)) ∈ support
      ((simulateQ (sourceDirectTracedMappedAdversaryImpl key.publicKey
        (materializePrecomputation key.cache key.secretKey))
        (adversary.main key.publicKey)).run (key.cache, [])) := by
    rw [← cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
      (materializePrecomputation key.cache key.secretKey)
      (adversary.main key.publicKey) ((key.cache, []), []) [], support_map]
    exact ⟨result, hresult, rfl⟩
  have hcache := freshEncodingCache_execution key.publicKey
    (materializePrecomputation key.cache key.secretKey) key.cache
    (adversary.main key.publicKey) _ hprojection result.1 hfresh hunqueried
  exact hcache.trans (keygen_cache_none_encodingInput key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) _ _)

theorem sourcePrefix_fresh_encoding_cached_implies_direct_query (adversary : XmssSecurity.Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixExecution adversary key))
    (hfresh : ¬ SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hcached : result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none) :
    CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness) ∈ result.2.2.hashInputs := by
  by_contra hunqueried
  exact hcached (sourcePrefix_fresh_encoding_unqueried adversary key hkey result hresult hfresh hunqueried)

theorem sourcePrefix_fresh_encoding_cached_positive_count (adversary : XmssSecurity.Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixExecution adversary key))
    (hfresh : ¬ SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hcached : result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none) :
    1 ≤ result.2.2.encodingInputCount key.secretKey.parameter := by
  have hmem := sourcePrefix_fresh_encoding_cached_implies_direct_query adversary key hkey
    result hresult hfresh hcached
  unfold AttackerActionTrace.encodingInputCount
  exact List.countP_pos_iff.mpr ⟨_, hmem, by simp⟩

/-- info: 'XmssSecurity.EUFCMA.sourcePrefix_fresh_encoding_cached_positive_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_fresh_encoding_cached_positive_count

end XmssSecurity.EUFCMA

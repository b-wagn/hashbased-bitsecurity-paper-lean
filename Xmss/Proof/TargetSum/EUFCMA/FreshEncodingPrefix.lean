import Xmss.Proof.TargetSum.EUFCMA.FreshEncoding
import Xmss.Proof.Generic.Direct.DecidingPrefixProjection
import Xmss.Proof.TargetSum.Direct.CountedSourceEncodingBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A cached standard-fresh forgery witnesses a direct encoding query in the
existing source-prefix trace. Free signing cannot supply that witness. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

theorem sourcePrefix_fresh_encoding_unqueried (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hfresh : ¬ Unforgeability.SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hunqueried : CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness) ∉ result.2.2.hashInputs) :
    result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) = none := by
  have hprojection : (result.1, (result.2.1.1.1, result.2.2)) ∈ support
      ((simulateQ (CappedExecution.sourceDirectTracedMappedAdversaryImpl key.publicKey
        (Keygen.materializePrecomputation key.cache key.secretKey))
        (adversary.main key.publicKey)).run (key.cache, [])) := by
    rw [← CappedExecution.cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
      (Keygen.materializePrecomputation key.cache key.secretKey)
      (adversary.main key.publicKey) ((key.cache, []), []) [], support_map]
    exact ⟨result, hresult, rfl⟩
  have hcache := freshEncodingCache_execution key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey) key.cache
    (adversary.main key.publicKey) _ hprojection result.1 hfresh
    (by simpa only [Keygen.materializePrecomputation_parameter] using hunqueried)
  rw [Keygen.materializePrecomputation_parameter] at hcache
  exact hcache.trans (Keygen.keygen_cache_none_encodingInput key.keyResult
    (CappedExecution.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) _ _)

theorem sourcePrefix_fresh_encoding_cached_implies_direct_query (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hfresh : ¬ Unforgeability.SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hcached : result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none) :
    CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness) ∈ result.2.2.hashInputs := by
  by_contra hunqueried
  exact hcached (sourcePrefix_fresh_encoding_unqueried adversary key hkey result hresult hfresh hunqueried)

theorem sourcePrefix_fresh_encoding_cached_positive_count (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hfresh : ¬ Unforgeability.SigningTranscript.ContainsRequest result.2.2.toSigningLog result.1)
    (hcached : result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none) :
    1 ≤ result.2.2.encodingInputCount key.secretKey.parameter := by
  have hmem := sourcePrefix_fresh_encoding_cached_implies_direct_query adversary key hkey
    result hresult hfresh hcached
  unfold CappedExecution.AttackerActionTrace.encodingInputCount
  exact List.countP_pos_iff.mpr ⟨_, hmem, by simp⟩

/-- info: 'Xmss.TargetSum.EUFCMA.sourcePrefix_fresh_encoding_cached_positive_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_fresh_encoding_cached_positive_count

end Xmss.TargetSum.EUFCMA

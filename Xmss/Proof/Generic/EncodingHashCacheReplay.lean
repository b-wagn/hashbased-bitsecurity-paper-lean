import Xmss.Proof.Generic.CacheReplayEval
import Xmss.Proof.Generic.HashInputLemmas

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

theorem CacheReplay.encodingHash_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Hashing.encodingHash parameter leafIndex message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    CacheView.encodingHash largerCache parameter leafIndex
      (message, randomness) = digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : Digest × QueryCache HashSpec =>
        (result.1, result.2)) <$> (randomOracle
          (CacheView.encodingInput parameter leafIndex
            (message, randomness))).run initialCache) := by
    simpa [Hashing.encodingHash, Hashing.tweakableHash,
      Hashing.oracleHash, CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := CacheReplay.randomOracle_query_caches
    (CacheView.encodingInput parameter leafIndex (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  have hcachedLarger := hle hcached
  rw [CacheView.encodingHash,
    CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]
  exact congrArg Prod.fst heq

/-- After an encoding query, the cache-aware decoder returns the decoded digest. -/
theorem CacheReplay.decodedEncoding_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Hashing.encodingHash parameter leafIndex message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    CacheView.decodedEncoding largerCache parameter leafIndex
      (message, randomness) = Code.decodeDigest digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : Digest × QueryCache HashSpec =>
        (result.1, result.2)) <$> (randomOracle
          (CacheView.encodingInput parameter leafIndex
            (message, randomness))).run initialCache) := by
    simpa [Hashing.encodingHash, Hashing.tweakableHash,
      Hashing.oracleHash, CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := CacheReplay.randomOracle_query_caches
    (CacheView.encodingInput parameter leafIndex (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  rw [CacheView.decodedEncoding_eq_of_cache_eq_some (hle hcached),
    CacheReplay.encodingHash_eq_of_run_support_of_cache_le parameter initialCache
      resultCache largerCache leafIndex message randomness digest hresult hle]

end Xmss.Generic

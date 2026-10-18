import XmssSecurity.Proof.Generic.CacheReplayEval
import XmssSecurity.Proof.Generic.HashInputLemmas

open OracleComp OracleSpec

namespace XmssSecurity.Generic

variable [Code]

theorem Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.encodingHash largerCache parameter leafIndex
      (message, randomness) = digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter leafIndex
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  have hcachedLarger := hle hcached
  rw [Concrete.CacheView.encodingHash,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]
  exact congrArg Prod.fst heq

/-- After an encoding query, the cache-aware decoder returns the decoded digest. -/
theorem Concrete.CacheReplay.decodedEncoding_eq_of_run_support_of_cache_le
    (parameter : PublicParameter)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (digest : Digest)
    (hresult : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run
          initialCache))
    (hle : resultCache ≤ largerCache) :
    Concrete.CacheView.decodedEncoding largerCache parameter leafIndex
      (message, randomness) = Code.decodeDigest digest := by
  have hmapped : (digest, resultCache) ∈ support
      ((fun result : HashOutput × QueryCache HashSpec =>
        (truncateHash result.1, result.2)) <$> (randomOracle
          (Concrete.CacheView.encodingInput parameter leafIndex
            (message, randomness))).run initialCache) := by
    simpa [Concrete.encodingHash, Concrete.tweakableHash,
      Concrete.oracleHash, Concrete.CacheView.encodingInput,
      map_eq_bind_pure_comp] using hresult
  rw [support_map] at hmapped
  obtain ⟨result, hquery, heq⟩ := hmapped
  have hcached := Concrete.CacheReplay.randomOracle_query_caches
    (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness))
    initialCache result.1 result.2 hquery
  rw [show result.2 = resultCache from congrArg Prod.snd heq] at hcached
  rw [Concrete.CacheView.decodedEncoding_eq_of_cache_eq_some (hle hcached),
    Concrete.CacheReplay.encodingHash_eq_of_run_support_of_cache_le parameter initialCache
      resultCache largerCache leafIndex message randomness digest hresult hle]

end XmssSecurity.Generic

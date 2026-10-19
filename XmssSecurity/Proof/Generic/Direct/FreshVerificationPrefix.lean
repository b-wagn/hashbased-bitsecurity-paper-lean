import XmssSecurity.Proof.Generic.Direct.PathVerificationProbability
import XmssSecurity.Proof.Generic.Direct.ZeroHashStructural

/-! Expose a fresh encoding digest before running the remaining verification. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Direct

theorem verificationPhase_run_fresh_cached (publicKey : PublicKey) (secretKey : SecretKey)
    (result : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hfresh : cache (forgeryEncodingInput publicKey result.1) = none) :
    (simulateQ romImpl (verificationPhase publicKey secretKey result)).run cache = (do
      let digest ← $ᵗ Digest
      (simulateQ romImpl (verificationPhase publicKey secretKey result)).run
        (cache.cacheQuery (forgeryEncodingInput publicKey result.1) digest)) := by
  unfold verificationPhase
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    simulateQ_romImpl_scheme_verify]
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
  simp only [bind_map_left, bind_assoc]
  apply bind_congr
  intro digest
  rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]

theorem fresh_encoding_prefix_support (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (result : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run initialCache))
    (hfresh : result.2 (forgeryEncodingInput publicKey result.1.1) = none) (digest : Digest) :
    (result.1, result.2.cacheQuery (forgeryEncodingInput publicKey result.1.1) digest) ∈ support
      ((simulateQ romImpl (adversaryPhase (withForgedEncodingQuery adversary) publicKey secretKey)).run
        initialCache) := by
  unfold adversaryPhase
  rw [run_simulateQ_withForgedEncodingQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨result, hresult, ?_⟩
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_pure, romImpl_inr]
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
  simp [uniformSampleImpl]

end XmssSecurity.Generic.Deciding

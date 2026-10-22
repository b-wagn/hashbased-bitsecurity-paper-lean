import Xmss.Proof.Generic.Direct.DecidingPrefixProgram
import Xmss.Proof.Generic.Direct.ForgedEncodingQuery

/-! The traced adversary prefix projects to the ordinary adversary phase. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic.Deciding

variable [Code]

open CappedExecution

theorem sourcePrefixExecution_phase_support (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (result : Forgery × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixExecution adversary key)) :
    ((result.1, result.2.2.toSigningLog), result.2.1.1.1) ∈ support
      ((simulateQ romImpl (adversaryPhase adversary key.publicKey
        (Keygen.materializePrecomputation key.cache key.secretKey))).run key.cache) := by
  let secret := Keygen.materializePrecomputation key.cache key.secretKey
  have hencoding : (result.1, result.2.1) ∈ support
      ((simulateQ (cappedEncodingTracedMappedAdversaryImpl key.publicKey secret)
        (adversary.main key.publicKey)).run ((key.cache, []), [])) := by
    rw [← cappedBothTracedMappedAdversaryImpl_projection key.publicKey secret
      (adversary.main key.publicKey) ((key.cache, []), []) [], support_map]
    exact ⟨result, hresult, rfl⟩
  have hsigning : (result.1, result.2.1.1) ∈ support
      ((simulateQ (cappedCacheTracedMappedAdversaryImpl key.publicKey secret)
        (adversary.main key.publicKey)).run (key.cache, [])) := by
    rw [← cappedEncodingTracedMappedAdversaryImpl_projection key.publicKey secret
      (adversary.main key.publicKey) (key.cache, []) [], support_map]
    exact ⟨(result.1, result.2.1), hencoding, rfl⟩
  have hlogProjection : (result.1, (result.2.1.1.1, result.2.1.1.2.toSigningLog)) ∈ support
      ((fun answer => (answer.1.1, (answer.2, answer.1.2))) <$>
        (((simulateQ (cappedMappedAdversaryImpl key.publicKey secret)
          (adversary.main key.publicKey)).run).run key.cache)) := by
    rw [← cappedCacheTracedMappedAdversaryImpl_log_projection_eq_mapped, support_map]
    exact ⟨(result.1, result.2.1.1), hsigning, rfl⟩
  rw [support_map] at hlogProjection
  obtain ⟨⟨⟨forgery, log⟩, cache⟩, hphase, heq⟩ := hlogProjection
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey secret
    (adversary.main key.publicKey) ((((key.cache, []), []), [])) result rfl hresult
  rw [hlogs] at hphase
  rw [cappedMappedAdversaryImpl, ← QueryImpl.simulateQ_writerTMapBase_run] at hphase
  exact hphase

theorem sourcePrefixExecution_withForgedEncodingQuery_cached (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixExecution (Direct.withForgedEncodingQuery adversary) key)) :
    result.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none := by
  have hphase := sourcePrefixExecution_phase_support (Direct.withForgedEncodingQuery adversary)
    key result hresult
  have hcached := Direct.adversaryPhase_withForgedEncodingQuery_cached adversary key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey) key.cache
    ((result.1, result.2.2.toSigningLog), result.2.1.1.1) hphase
  have hparameter := keygen_parameter_eq key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  change key.publicKey.parameter = key.secretKey.parameter at hparameter
  change result.2.1.1.1 (CacheView.encodingInput key.publicKey.parameter result.1.epoch
    (result.1.message, result.1.signature.randomness)) ≠ none at hcached
  rw [hparameter] at hcached
  exact hcached

end Xmss.Generic.Deciding

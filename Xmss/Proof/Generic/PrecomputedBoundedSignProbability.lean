import Xmss.Proof.Generic.PrecomputedBoundedSignCache
import Xmss.Proof.Generic.SignCacheHitProbability
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

set_option maxRecDepth 100000

noncomputable def Signing.precomputedSignBoundedAttemptsContinuation
    (attempts : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (result : Option Signature × QueryCache HashSpec) :
    ProbComp (Option Signature × QueryCache HashSpec) :=
  match result.1 with
  | some signature => pure (some signature, result.2)
  | none => (simulateQ romImpl
      (Signing.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run result.2

attribute [irreducible] Signing.precomputedSignBoundedAttemptsContinuation

theorem Signing.precomputedSignBoundedAttempts_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Signing.precomputedSignBoundedAttempts (attempts + 1) secretKey leafIndex message)).run
        cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))).run cache >>=
          Signing.precomputedSignBoundedAttemptsContinuation attempts secretKey leafIndex
            message) := by
  rw [Signing.precomputedSignBoundedAttempts, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl
        (liftM Signing.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Signing.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Signing.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Signing.signingRandomness cache
  rw [hsampleRun, Signing.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result <;> simp [Signing.precomputedSignBoundedAttemptsContinuation]

set_option linter.constructorNameAsVariable false in
theorem Signing.precomputedSignBoundedAttempts_encodingInput_referenceCache_hit_le_cachedCount
    (attempts : Nat) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        referenceCache (CacheView.encodingInput secretKey.parameter leafIndex
          (message, signature.randomness)) = some output |
      (simulateQ romImpl
        (Signing.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run
          workingCache] ≤
      (attempts : ℝ≥0∞) *
        cachedEncodingEntryCount referenceCache secretKey.parameter leafIndex *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [Signing.precomputedSignBoundedAttempts]
  | succ attempts ih =>
      rw [Signing.precomputedSignBoundedAttempts_run_succ_eq]
      refine (probEvent_bind_le_probEvent_add
        (p := fun randomness : Randomness => ∃ output,
          referenceCache (CacheView.encodingInput secretKey.parameter leafIndex
            (message, randomness)) = some output)
        (ε := (attempts : ℝ≥0∞) *
          cachedEncodingEntryCount referenceCache secretKey.parameter leafIndex *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
      · intro randomness _hrandomness hmiss
        refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hresult : attemptResult.1 with
        | none =>
            simpa [Signing.precomputedSignBoundedAttemptsContinuation, hresult] using
              ih attemptResult.2
        | some signature =>
            refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hsupport hevent
            have hsupport' : result ∈ support
                (pure (some signature, attemptResult.2) :
                  ProbComp (Option Signature × QueryCache HashSpec)) := by
              simpa [Signing.precomputedSignBoundedAttemptsContinuation, hresult] using
                hsupport
            obtain ⟨found, hfound, output, hhit⟩ := hevent
            have hreturned : result.1 = some signature := by
              simpa only [support_pure, Set.mem_singleton_iff] using
                congrArg Prod.fst hsupport'
            have hsignature : signature = found :=
              Option.some.inj (hreturned.symm.trans hfound)
            have hrandomness :=
              Signing.precomputedSignAttempt_some_randomness secretKey leafIndex message
                randomness workingCache attemptResult.2 signature ?_
            · apply hmiss
              rw [← hsignature] at hhit
              rw [hrandomness] at hhit
              exact ⟨output, hhit⟩
            · have heq : attemptResult = (some signature, attemptResult.2) :=
                Prod.ext hresult rfl
              rw [← heq]
              exact hattempt
      · calc
          _ ≤ cachedEncodingEntryCount referenceCache secretKey.parameter leafIndex *
                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ +
              (attempts : ℝ≥0∞) *
                cachedEncodingEntryCount referenceCache secretKey.parameter leafIndex *
                ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ :=
            add_le_add
              (uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntryCount
                secretKey.parameter leafIndex message referenceCache) le_rfl
          _ = _ := by
            push_cast
            ring

set_option linter.constructorNameAsVariable false in
theorem Signing.precomputedCappedSign_encodingInput_initialCache_hit_le_cachedCount
    (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun result : Option Signature × QueryCache HashSpec =>
      ∃ signature, result.1 = some signature ∧ ∃ output,
        cache (CacheView.encodingInput secretKey.parameter leafIndex
          (message, signature.randomness)) = some output |
      (simulateQ romImpl
        (Signing.precomputedCappedSign secretKey leafIndex message)).run cache] ≤
      (Code.signingAttemptLimit : ℝ≥0∞) *
        cachedEncodingEntryCount cache secretKey.parameter leafIndex *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [Signing.precomputedCappedSign]
  exact Signing.precomputedSignBoundedAttempts_encodingInput_referenceCache_hit_le_cachedCount
    Code.signingAttemptLimit secretKey leafIndex message cache cache

end Xmss.Generic

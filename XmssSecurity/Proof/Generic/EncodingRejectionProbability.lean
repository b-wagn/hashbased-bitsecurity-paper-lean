import XmssSecurity.Proof.Generic.EncodingProbability
import XmssSecurity.Proof.Generic.PrecomputedBoundedSignProbability
import XmssSecurity.Proof.Generic.RandomOracle
import XmssSecurity.Proof.Generic.CappedEncodingPrehitExpectedBound

/-! Failure bounds for capped encoding search, including repeated randomizers. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic

variable [Code]

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

theorem cachedEncodingEntryCount_le_inputCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) :
    cachedEncodingEntryCount cache parameter leafIndex ≤ cachedEncodingInputCount cache parameter := by
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  intro entry hentry
  exact ⟨hentry.1, by simp [hentry.2]⟩

theorem Concrete.precomputedSignAttempt_run_fresh
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : cache (CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness)) = none) :
    (simulateQ randomOracle
      (precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))).run cache =
      (fun output : HashOutput =>
        ((Code.decodeDigest (truncateHash output)).map
          (precomputedSignWithEncoding secretKey leafIndex randomness),
        cache.cacheQuery (CacheView.encodingInput secretKey.parameter leafIndex
          (message, randomness)) output)) <$> ($ᵗ HashOutput) := by
  unfold precomputedSignAttempt encodingHash tweakableHash oracleHash
  simp only [bind_assoc, pure_bind, simulateQ_bind, HasQuery.instOfMonadLift_query,
    simulateQ_spec_query, StateT.run_bind]
  change (randomOracle (CacheView.encodingInput secretKey.parameter leafIndex
    (message, randomness))).run cache >>= _ = _
  rw [randomOracle_run_none_eq_uniformHashOutput _ _ hfresh]
  simp only [uniformHashOutput, bind_map_left]
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro output
  simp only [Function.comp_apply]
  cases Code.decodeDigest (truncateHash output) <;> simp

theorem Code.probEvent_invalidDigest_uniformHashOutput :
    Pr[fun output : HashOutput => ¬ ValidDigest (truncateHash output) | $ᵗ HashOutput] =
      1 - Code.acceptanceProbability := by
  have hvalid : Pr[fun output : HashOutput => ValidDigest (truncateHash output) |
      $ᵗ HashOutput] = Code.acceptanceProbability := by
    change Pr[ValidDigest ∘ truncateHash | $ᵗ HashOutput] = _
    rw [← probEvent_map, probEvent_def, Rom.evalDist_truncate_uniformHashOutput,
      ← probEvent_def]
    exact Code.probEvent_validDigest_uniform
  apply ENNReal.eq_sub_of_add_eq Code.acceptanceProbability_ne_top
  simpa only [hvalid, add_comm, probFailure_uniformSample, tsub_zero] using
    probEvent_compl ($ᵗ HashOutput) (fun output => ValidDigest (truncateHash output))

private theorem probEvent_bind_le_event_mul {α β : Type} (first : ProbComp α)
    (next : α → ProbComp β) (event : β → Prop) (gate : α → Prop) [DecidablePred gate]
    (bound : ℝ≥0∞)
    (hbound : ∀ x, Pr[event | next x] ≤ if gate x then bound else 0) :
    Pr[event | first >>= next] ≤ Pr[gate | first] * bound := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : gate x
  · simpa only [if_pos hx] using mul_le_mul' (le_refl (Pr[= x | first])) (hbound x)
  · simpa only [if_neg hx, mul_zero, zero_mul] using
      mul_le_mul' (le_refl (Pr[= x | first])) (hbound x)

/-- A capped search can fail through rejection or through repeated randomizers. The latter
term also covers any encoding entries already present in the starting cache. -/
theorem Concrete.precomputedSignBoundedAttempts_failure_le
    (attempts : ℕ) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) (known : ℕ)
    (hknown : cachedEncodingInputCount cache secretKey.parameter ≤ known) :
    Pr[fun result : Option Signature × QueryCache HashSpec => result.1 = none |
      (simulateQ romImpl (precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run
        cache] ≤
      (1 - Code.acceptanceProbability) ^ attempts +
        (attempts : ℝ≥0∞) * (known + attempts) * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction attempts generalizing cache known with
  | zero => simp [precomputedSignBoundedAttempts]
  | succ attempts ih =>
      rw [precomputedSignBoundedAttempts_run_succ_eq]
      let a : ℝ≥0∞ := 1 - Code.acceptanceProbability
      let r : ℝ≥0∞ := ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹
      let b : ℝ≥0∞ := a ^ attempts + (attempts : ℝ≥0∞) * (known + 1 + attempts) * r
      have ha : a ≤ 1 := tsub_le_self
      have hsplit : Pr[fun result : Option Signature × QueryCache HashSpec => result.1 = none |
          ($ᵗ Randomness) >>= fun randomness =>
            (simulateQ randomOracle
              (precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature))).run cache >>=
              precomputedSignBoundedAttemptsContinuation attempts secretKey leafIndex message] ≤
          (known : ℝ≥0∞) * r + a * b := by
        refine (probEvent_bind_le_probEvent_add
          (p := fun randomness => ∃ output, cache (CacheView.encodingInput secretKey.parameter
            leafIndex (message, randomness)) = some output) (ε := a * b) ?_).trans ?_
        · intro randomness _ hmiss
          have hfresh : cache (CacheView.encodingInput secretKey.parameter leafIndex
              (message, randomness)) = none := by
            cases hcache : cache (CacheView.encodingInput secretKey.parameter leafIndex
              (message, randomness)) with
            | none => rfl
            | some value => exact (hmiss ⟨value, hcache⟩).elim
          rw [precomputedSignAttempt_run_fresh _ _ _ _ _ hfresh, bind_map_left]
          refine (probEvent_bind_le_event_mul _ _ _
            (fun output => ¬ Code.ValidDigest (truncateHash output)) b ?_).trans_eq ?_
          · intro output
            have hnext : cachedEncodingInputCount
                (cache.cacheQuery (CacheView.encodingInput secretKey.parameter leafIndex
                  (message, randomness)) output) secretKey.parameter ≤ (known + 1 : ℕ) := by
              calc
                _ ≤ cachedEncodingInputCount cache secretKey.parameter + 1 := by
                  simpa using cachedEncodingInputCount_cacheQuery_le cache secretKey.parameter
                    (CacheView.encodingInput secretKey.parameter leafIndex (message, randomness)) output
                _ ≤ _ := by simpa using add_le_add hknown (le_refl (1 : ℝ≥0∞))
            cases hdecode : Code.decodeDigest (truncateHash output) with
            | none =>
                simpa [precomputedSignBoundedAttemptsContinuation, Code.ValidDigest,
                  hdecode, b, a, r, Nat.cast_add, Nat.cast_one] using
                  ih (cache.cacheQuery (CacheView.encodingInput secretKey.parameter leafIndex
                    (message, randomness)) output) (known + 1) hnext
            | some encoding =>
                simp [precomputedSignBoundedAttemptsContinuation]
          · rw [Code.probEvent_invalidDigest_uniformHashOutput]
        · apply add_le_add _ le_rfl
          exact (uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntryCount
            secretKey.parameter leafIndex message cache).trans
              (mul_le_mul' ((cachedEncodingEntryCount_le_inputCount cache
                secretKey.parameter leafIndex).trans hknown) le_rfl)
      refine hsplit.trans ?_
      change (known : ℝ≥0∞) * r + a * b ≤ a ^ (attempts + 1) +
        ((attempts + 1 : ℕ) : ℝ≥0∞) * (known + (attempts + 1 : ℕ)) * r
      calc
        (known : ℝ≥0∞) * r + a * b = a ^ (attempts + 1) +
            ((known : ℝ≥0∞) + a * ((attempts : ℝ≥0∞) * (known + 1 + attempts))) * r := by
          dsimp [b]
          rw [pow_succ]
          ring
        _ ≤ a ^ (attempts + 1) +
            ((known : ℝ≥0∞) + (attempts : ℝ≥0∞) * (known + 1 + attempts)) * r := by
          exact add_le_add le_rfl (mul_le_mul'
            (add_le_add le_rfl (mul_le_of_le_one_left' ha)) le_rfl)
        _ ≤ _ := by
          apply add_le_add le_rfl
          apply mul_le_mul' _ le_rfl
          exact_mod_cast (show known + attempts * (known + 1 + attempts) ≤
            (attempts + 1) * (known + (attempts + 1)) by nlinarith)

private theorem real_rejection_power_mul_le_one (p : ℝ) (hpone : p ≤ 1)
    (attempts : ℕ) : (1 - p) ^ attempts * (1 + attempts * p) ≤ 1 := by
  induction attempts with
  | zero => simp
  | succ attempts ih =>
      have hstep : (1 - p) * (1 + ((attempts + 1 : ℕ) : ℝ) * p) ≤
          1 + (attempts : ℝ) * p := by
        push_cast
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ attempts + 1 by positivity) (sq_nonneg p)]
      calc
        _ = (1 - p) ^ attempts * ((1 - p) * (1 + ((attempts + 1 : ℕ) : ℝ) * p)) := by
          rw [pow_succ, mul_assoc]
        _ ≤ (1 - p) ^ attempts * (1 + (attempts : ℝ) * p) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hpone) _)
        _ ≤ 1 := ih

/-- A rational geometric-tail bound avoids evaluating a power with billions of factors. -/
theorem Code.rejection_power_le (p : ℝ≥0∞) (hp : p ≤ 1) (attempts : ℕ) :
    (1 - p) ^ attempts ≤ 1 / (1 + (attempts : ℝ≥0∞) * p) := by
  have hpfinite : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hpreal : p.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hpfinite ENNReal.one_ne_top).mpr hp
  have hreal := real_rejection_power_mul_le_one p.toReal hpreal attempts
  have hdenom : (0 : ℝ) < 1 + (attempts : ℝ) * p.toReal := by positivity
  have hbound := (le_div_iff₀ hdenom).mpr hreal
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,
    ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simpa only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast] using hbound

/-- The signer's failure bound: from a fresh cache, all `A_max` attempts reject, or two attempts
repeat a randomizer, with probability below `1/32`. Each code proves it (`Code.SignerBound`). -/
class Code.SignerBound : Prop where
  capped_rejection_bound_lt :
    (1 - Code.acceptanceProbability) ^ Code.signingAttemptLimit +
      (Code.signingAttemptLimit : ℝ≥0∞) * Code.signingAttemptLimit *
        ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 32

variable [Code.SignerBound]

/-- In the reference scheme, a fresh signing request succeeds with probability greater than
`31/32`; randomizer repetitions are included in the failure bound. -/
theorem Concrete.precomputedCappedSign_failure_lt
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : cachedEncodingInputCount cache secretKey.parameter = 0) :
    Pr[fun result : Option Signature × QueryCache HashSpec => result.1 = none |
      (simulateQ romImpl (precomputedCappedSign secretKey leafIndex message)).run cache] <
      1 / 32 := by
  rw [precomputedCappedSign]
  have hbound := precomputedSignBoundedAttempts_failure_le Code.signingAttemptLimit secretKey leafIndex
    message cache 0 (by simpa using hcache.le)
  simp only [Nat.cast_zero, zero_add] at hbound
  exact hbound.trans_lt Code.SignerBound.capped_rejection_bound_lt

theorem Concrete.precomputedCappedSign_success_gt
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : cachedEncodingInputCount cache secretKey.parameter = 0) :
    31 / 32 < Pr[fun result : Option Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (precomputedCappedSign secretKey leafIndex message)).run cache] := by
  let computation :=
    (simulateQ romImpl (precomputedCappedSign secretKey leafIndex message)).run cache
  have hfailure := precomputedCappedSign_failure_lt secretKey leafIndex message cache hcache
  have hsum : Pr[fun result => result.1 = none | computation] +
      Pr[fun result => result.1 ≠ none | computation] = 1 := by
    simpa only [probFailure_of_liftM_PMF, tsub_zero] using
      probEvent_compl computation (fun result => result.1 = none)
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hsumReal
  have hfailureReal := (ENNReal.toReal_lt_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_lt_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hfailureReal ⊢
  change (Pr[fun result => result.1 = none | computation]).toReal < 1 / 32 at hfailureReal
  change 31 / 32 < (Pr[fun result => result.1 ≠ none | computation]).toReal
  linarith

/-- The reference key-generation cache meets the fresh-encoding condition. -/
theorem Concrete.precomputedCappedSign_success_after_keygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    31 / 32 < Pr[fun result : Option Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (precomputedCappedSign keyResult.1.2 leafIndex message)).run keyResult.2] :=
  precomputedCappedSign_success_gt _ _ _ _ (keygen_cachedEncodingInputCount_eq_zero keyResult hkey)

/-- info: 'XmssSecurity.Generic.Concrete.precomputedCappedSign_success_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.precomputedCappedSign_success_after_keygen

end XmssSecurity.Generic

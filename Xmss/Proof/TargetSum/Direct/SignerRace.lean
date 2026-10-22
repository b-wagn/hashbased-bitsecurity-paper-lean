import Xmss.Proof.Generic.EncodingRejectionProbability
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-!
# The signer's race between cached and fresh randomizers

A signing request draws randomizers until a digest decodes. A randomizer whose encoding input is
cached with a decodable digest is accepted at once; a fresh one is accepted with probability `p`.
So with `k` attempts left, the signer accepts a randomizer from a set `S` of cached decodable
randomizers with probability at most `|S| / (v + p (N - n - k))`, where `v` counts the cached
decodable randomizers it accepts from, `n` all cached randomizers, and `N = 2^128`
(`precomputedSignBoundedAttempts_expectedCost_le`, with a second weighted class `W \ S`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

theorem Signing.precomputedSignAttempt_run_cached
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (output : Digest)
    (hcached : cache (CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness)) = some output) :
    (simulateQ randomOracle
      (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Generic.Signature))).run cache =
      pure ((Code.decodeDigest (output)).map
        (Generic.Signing.precomputedSignWithEncoding secretKey leafIndex randomness), cache) := by
  unfold Generic.Signing.precomputedSignAttempt Generic.Hashing.encodingHash Generic.Hashing.tweakableHash Generic.Hashing.oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query,
    simulateQ_spec_query, StateT.run_bind]
  change (randomOracle (CacheView.encodingInput secretKey.parameter leafIndex
    (message, randomness))).run cache >>= _ = _
  rw [randomOracle, QueryImpl.withCaching_run_some _ hcached, pure_bind]
  cases Code.decodeDigest (output) <;> simp

namespace Direct

variable (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)

/-- The randomizers whose encoding input for `message` at `leafIndex` is cached. -/
noncomputable def cachedRandomizersAt (cache : QueryCache HashSpec) : Finset Randomness := by
  classical
  exact Finset.univ.filter fun randomness =>
    cache (CacheView.encodingInput parameter leafIndex (message, randomness)) ≠ none

/-- The encoding input of `randomness` is cached with a decodable digest. -/
def DecodableAt (cache : QueryCache HashSpec) (randomness : Randomness) : Prop :=
  ∃ output, cache (CacheView.encodingInput parameter leafIndex (message, randomness)) =
    some output ∧ Code.ValidDigest (output)

/-- The cost of a signing outcome: `1` for a randomizer in `S`, `weight` for one in `W \ S`, and
`0` otherwise. -/
noncomputable def raceCost (S W : Finset Randomness) (weight : ℝ≥0∞) :
    Option Generic.Signature → ℝ≥0∞
  | none => 0
  | some signature =>
      if signature.randomness ∈ S then 1 else if signature.randomness ∈ W then weight else 0

/-- The race bound `(|S| + weight |W \ S|) / (|W| + p (N - n - k))`. -/
noncomputable def raceBound (S W : Finset Randomness) (weight : ℝ≥0∞) (cached attempts : ℕ) :
    ℝ≥0∞ :=
  ((S.card : ℝ≥0∞) + weight * ((W \ S).card : ℝ≥0∞)) /
    ((W.card : ℝ≥0∞) + TargetSum.acceptanceProbability *
      ((2 ^ digestBits - cached - attempts : ℕ) : ℝ≥0∞))

theorem raceBound_mono_attempts (S W : Finset Randomness) (weight : ℝ≥0∞) (cached : ℕ)
    {attempts attempts' : ℕ} (h : attempts ≤ attempts') :
    raceBound S W weight cached attempts ≤ raceBound S W weight cached attempts' := by
  unfold raceBound
  gcongr

theorem raceBound_succ_cached (S W : Finset Randomness) (weight : ℝ≥0∞) (cached attempts : ℕ) :
    raceBound S W weight (cached + 1) attempts = raceBound S W weight cached (attempts + 1) := by
  unfold raceBound
  congr 4
  omega

theorem cachedRandomizersAt_cacheQuery (cache : QueryCache HashSpec) (randomness : Randomness)
    (output : Digest) :
    cachedRandomizersAt parameter leafIndex message
        (cache.cacheQuery (CacheView.encodingInput parameter leafIndex
          (message, randomness)) output) =
      insert randomness (cachedRandomizersAt parameter leafIndex message cache) := by
  classical
  ext other
  simp only [cachedRandomizersAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hother : other = randomness
  · subst hother
    simp
  · have hne : CacheView.encodingInput parameter leafIndex (message, other) ≠
        CacheView.encodingInput parameter leafIndex (message, randomness) := by
      intro h
      exact hother (congrArg Prod.snd (CacheView.encodingInput_injective parameter
        leafIndex h))
    rw [QueryCache.cacheQuery_of_ne _ _ hne]
    simp [hother]

theorem DecodableAt.mono {cache cache' : QueryCache HashSpec} (hle : cache ≤ cache')
    {randomness : Randomness} (h : DecodableAt parameter leafIndex message cache randomness) :
    DecodableAt parameter leafIndex message cache' randomness := by
  obtain ⟨output, hcache, hvalid⟩ := h
  exact ⟨output, hle hcache, hvalid⟩

theorem DecodableAt.mem_cached {cache : QueryCache HashSpec} {randomness : Randomness}
    (h : DecodableAt parameter leafIndex message cache randomness) :
    randomness ∈ cachedRandomizersAt parameter leafIndex message cache := by
  classical
  obtain ⟨output, hcache, _⟩ := h
  simp [cachedRandomizersAt, hcache]

/-- The arithmetic of one race step. -/
theorem race_step_le (a b v n N : ℕ) (p weight bound rest : ℝ≥0∞)
    (hv : a + b = v) (hvn : v ≤ n) (hnN : n ≤ N) (hp : p ≤ 1)
    (hbound : bound = ((a : ℝ≥0∞) + weight * b) / ((v : ℝ≥0∞) + p * rest))
    (hrest : rest ≤ ((N - n : ℕ) : ℝ≥0∞)) :
    ((a : ℝ≥0∞) + weight * b + ((n - v : ℕ) : ℝ≥0∞) * bound +
        ((N - n : ℕ) : ℝ≥0∞) * ((1 - p) * bound)) ≤ (N : ℝ≥0∞) * bound := by
  by_cases hden : (v : ℝ≥0∞) + p * rest = 0
  · have hvzero : v = 0 := by
      have := (add_eq_zero.mp hden).1
      exact_mod_cast this
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    simp [hbound]
  have hnum : (a : ℝ≥0∞) + weight * b ≤ ((v : ℝ≥0∞) + p * ((N - n : ℕ) : ℝ≥0∞)) * bound := by
    by_cases htop : (a : ℝ≥0∞) + weight * b = ⊤
    · have hbtop : bound = ⊤ := by
        rw [hbound, htop]
        exact ENNReal.top_div_of_ne_top (by
          refine ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ?_⟩
          exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hp)
            (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) hrest))
      rw [hbtop, ENNReal.mul_top]
      · exact le_top
      · intro hzero
        apply hden
        exact le_antisymm ((add_le_add le_rfl (mul_le_mul' le_rfl hrest)).trans hzero.le) zero_le
    calc
      (a : ℝ≥0∞) + weight * b = ((v : ℝ≥0∞) + p * rest) * bound := by
        rw [hbound, ENNReal.mul_div_cancel hden (by
          refine ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ?_⟩
          exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hp)
            (ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) hrest))]
      _ ≤ _ := by gcongr
  have htotal : (N : ℝ≥0∞) = (v : ℝ≥0∞) + ((n - v : ℕ) : ℝ≥0∞) + ((N - n : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_add, ← Nat.cast_add]
    congr 1
    omega
  have hsplit : ((N - n : ℕ) : ℝ≥0∞) =
      ((N - n : ℕ) : ℝ≥0∞) * p + ((N - n : ℕ) : ℝ≥0∞) * (1 - p) := by
    rw [← mul_add, add_tsub_cancel_of_le hp, mul_one]
  calc
    _ ≤ ((v : ℝ≥0∞) + p * ((N - n : ℕ) : ℝ≥0∞)) * bound + ((n - v : ℕ) : ℝ≥0∞) * bound +
          ((N - n : ℕ) : ℝ≥0∞) * ((1 - p) * bound) := by
      gcongr
    _ = ((v : ℝ≥0∞) + ((n - v : ℕ) : ℝ≥0∞) +
          (((N - n : ℕ) : ℝ≥0∞) * p + ((N - n : ℕ) : ℝ≥0∞) * (1 - p))) * bound := by
      ring
    _ = _ := by rw [← hsplit, ← htotal]

theorem acceptanceProbability_le_one : TargetSum.acceptanceProbability ≤ 1 :=
  TargetSum.acceptanceProbability_upper.le.trans
    (ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.one_le_two_pow))

theorem sum_indicator_const (T : Finset Randomness) (value : ℝ≥0∞) :
    (∑ randomness, if randomness ∈ T then value else 0) = (T.card : ℝ≥0∞) * value := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- With `attempts` attempts left, the expected race cost is at most the race bound. -/
theorem precomputedSignBoundedAttempts_expectedCost_le (secretKey : Generic.SecretKey)
    (leafIndex : LeafIndex) (message : Message) (S W : Finset Randomness) (weight : ℝ≥0∞)
    (hSW : S ⊆ W) :
    ∀ (attempts : ℕ) (cache : QueryCache HashSpec),
      (∀ randomness ∈ W, DecodableAt secretKey.parameter leafIndex message cache randomness) →
      ∑' result, Pr[= result | (simulateQ romImpl
          (Signing.precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run
            cache] * raceCost S W weight result.1 ≤
        raceBound S W weight
          (cachedRandomizersAt secretKey.parameter leafIndex message cache).card attempts := by
  intro attempts
  induction attempts with
  | zero =>
      intro cache _
      simp [Signing.precomputedSignBoundedAttempts, raceCost]
  | succ attempts ih =>
      intro cache hW
      classical
      let cached := cachedRandomizersAt secretKey.parameter leafIndex message cache
      let bound := raceBound S W weight cached.card (attempts + 1)
      have hWcached : W ⊆ cached := fun randomness hmem => (hW randomness hmem).mem_cached
      let f : Randomness → ℝ≥0∞ := fun randomness =>
        (if randomness ∈ S then 1 else 0) + (if randomness ∈ W \ S then weight else 0) +
          (if randomness ∈ cached \ W then bound else 0) +
          (if randomness ∈ Finset.univ \ cached then
            (1 - TargetSum.acceptanceProbability) * bound else 0)
      have hstep : ∀ randomness,
          ∑' result, Pr[= result | (simulateQ randomOracle
              (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Generic.Signature))).run cache >>=
              Signing.precomputedSignBoundedAttemptsContinuation attempts secretKey leafIndex
                message] * raceCost S W weight result.1 ≤ f randomness := by
        intro randomness
        rw [tsum_probOutput_bind_mul]
        by_cases hcachedR : randomness ∈ cached
        · obtain ⟨output, houtput⟩ : ∃ output, cache (CacheView.encodingInput
              secretKey.parameter leafIndex (message, randomness)) = some output := by
            have := hcachedR
            simp only [cached, cachedRandomizersAt, Finset.mem_filter, Finset.mem_univ,
              true_and] at this
            exact Option.ne_none_iff_exists'.mp this
          rw [Signing.precomputedSignAttempt_run_cached secretKey leafIndex message randomness
            cache output houtput, tsum_probOutput_pure_mul]
          cases hdecode : Code.decodeDigest (output) with
          | some encoding =>
              simp only [Option.map_some, Signing.precomputedSignBoundedAttemptsContinuation,
                tsum_probOutput_pure_mul, raceCost, Generic.Signing.precomputedSignWithEncoding]
              by_cases hS : randomness ∈ S
              · simp [f, hS]
                exact le_add_right (le_add_right le_rfl)
              · by_cases hWm : randomness ∈ W
                · simp [f, hS, hWm]
                · simp [hS, hWm]
          | none =>
              have hnotW : randomness ∉ W := by
                intro hmem
                obtain ⟨found, hfound, hvalid⟩ := hW randomness hmem
                rw [houtput, Option.some.injEq] at hfound
                subst hfound
                obtain ⟨encoding, hencoding⟩ := hvalid
                rw [hencoding] at hdecode
                simp at hdecode
              have hnotS : randomness ∉ S := fun hmem => hnotW (hSW hmem)
              simp only [Option.map_none, Signing.precomputedSignBoundedAttemptsContinuation]
              refine (ih cache hW).trans ?_
              have hf : f randomness = bound := by
                simp [f, hnotS, hnotW, hcachedR]
              rw [hf]
              exact raceBound_mono_attempts S W weight _ (Nat.le_succ attempts)
        · have hfresh : cache (CacheView.encodingInput secretKey.parameter leafIndex
              (message, randomness)) = none := by
            simpa [cached, cachedRandomizersAt] using hcachedR
          have hnotW : randomness ∉ W := fun hmem => hcachedR (hWcached hmem)
          have hnotS : randomness ∉ S := fun hmem => hnotW (hSW hmem)
          rw [Signing.precomputedSignAttempt_run_fresh secretKey leafIndex message randomness
            cache hfresh, tsum_probOutput_map_mul]
          calc
            _ ≤ ∑' output : Digest, Pr[= output | ($ᵗ Digest)] *
                (if Code.ValidDigest (output) then 0 else bound) := by
              refine ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl ?_
              cases hdecode : Code.decodeDigest (output) with
              | some encoding =>
                  have hvalid : Code.ValidDigest (output) := ⟨encoding, hdecode⟩
                  simp [Signing.precomputedSignBoundedAttemptsContinuation, raceCost,
                    Generic.Signing.precomputedSignWithEncoding, hnotS, hnotW, hvalid]
              | none =>
                  have hinvalid : ¬ Code.ValidDigest (output) := by
                    rintro ⟨encoding, hencoding⟩
                    rw [hencoding] at hdecode
                    simp at hdecode
                  simp only [Option.map_none, Signing.precomputedSignBoundedAttemptsContinuation,
                    if_neg hinvalid]
                  refine (ih _ fun other hother =>
                    (hW other hother).mono _ _ _ (QueryCache.le_cacheQuery _ hfresh)).trans (le_of_eq ?_)
                  rw [cachedRandomizersAt_cacheQuery, Finset.card_insert_of_notMem hcachedR,
                    raceBound_succ_cached]
            _ = Pr[fun output : Digest => ¬ Code.ValidDigest (output) |
                  $ᵗ Digest] * bound := by
              rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
              refine tsum_congr fun output => ?_
              by_cases hvalid : Code.ValidDigest (output) <;> simp [hvalid]
            _ = f randomness := by
              rw [Code.probEvent_invalidDigest_uniformHashOutput]
              simp [f, hnotS, hnotW, hcachedR, code_acceptanceProbability]
      rw [Signing.precomputedSignBoundedAttempts_run_succ_eq, tsum_probOutput_bind_mul]
      have hcard : (Fintype.card Randomness : ℝ≥0∞) = ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
        rw [card_randomness]
      calc
        _ ≤ ∑' randomness : Randomness, (Fintype.card Randomness : ℝ≥0∞)⁻¹ * f randomness := by
          refine ENNReal.tsum_le_tsum fun randomness => ?_
          rw [probOutput_uniformSample]
          exact mul_le_mul' le_rfl (hstep randomness)
        _ = (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
            ((S.card : ℝ≥0∞) + weight * ((W \ S).card : ℝ≥0∞) +
              (((cached.card - W.card : ℕ) : ℝ≥0∞)) * bound +
              (((2 ^ digestBits - cached.card : ℕ) : ℝ≥0∞)) *
                ((1 - TargetSum.acceptanceProbability) * bound)) := by
          have hsum : ∑ randomness, f randomness =
              (S.card : ℝ≥0∞) + weight * ((W \ S).card : ℝ≥0∞) +
                (((cached.card - W.card : ℕ) : ℝ≥0∞)) * bound +
                (((2 ^ digestBits - cached.card : ℕ) : ℝ≥0∞)) *
                  ((1 - TargetSum.acceptanceProbability) * bound) := by
            simp only [f, Finset.sum_add_distrib, sum_indicator_const]
            rw [Finset.card_sdiff_of_subset hWcached, Finset.card_sdiff_of_subset
              (Finset.subset_univ cached), Finset.card_univ, card_randomness]
            ring
          rw [tsum_fintype, ← Finset.mul_sum, hsum]
        _ ≤ (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
            (((2 ^ digestBits : ℕ) : ℝ≥0∞) * bound) := by
          refine mul_le_mul' le_rfl (race_step_le S.card (W \ S).card W.card cached.card
            (2 ^ digestBits) TargetSum.acceptanceProbability weight bound
            ((2 ^ digestBits - cached.card - (attempts + 1) : ℕ) : ℝ≥0∞) ?_
            (Finset.card_le_card hWcached) ?_ acceptanceProbability_le_one rfl ?_)
          · rw [Finset.card_sdiff_of_subset hSW]
            have := Finset.card_le_card hSW
            omega
          · have := Finset.card_le_univ cached
            rw [card_randomness] at this
            exact this
          · exact_mod_cast Nat.sub_le _ _
        _ = bound := by
          rw [hcard, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

end Direct

end Xmss.TargetSum

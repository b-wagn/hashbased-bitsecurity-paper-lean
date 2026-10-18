import XmssSecurity.Proof.TargetSum.Direct.CollisionStatistics
import XmssSecurity.Proof.TargetSum.Direct.CollisionMath
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-!
# The collision potential of an epoch

`leafPotential q parameter cache leafIndex` instantiates the potential of `CollisionMath` with
`N = 2^128`, `D = 2^128 - 2^32`, `p` the probability that a uniform digest decodes, and
`q' = q + 1`, reading its counts off the cache (`CollisionStatistics`). One fresh query at the
epoch raises its expectation by at most `collisionRate q` (`expected_leafPotential_cacheQuery_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct.Collision

open CollisionMath

noncomputable def realN : ℝ := 2 ^ 128
noncomputable def realD : ℝ := 2 ^ 128 - 2 ^ 32
noncomputable def realM : ℝ := 2 ^ 70
noncomputable def realβ : ℝ := 2 ^ 78
noncomputable def realP : ℝ := TargetSum.acceptanceProbability.toReal

theorem realP_pos : 0 < realP :=
  ENNReal.toReal_pos (ne_of_gt TargetSum.acceptanceProbability_pos)
    TargetSum.acceptanceProbability_ne_top

theorem realP_le_one : realP ≤ 1 := by
  have := (ENNReal.toReal_le_toReal TargetSum.acceptanceProbability_ne_top
    ENNReal.one_ne_top).mpr acceptanceProbability_le_one
  simpa [realP] using this

theorem realP_ge : 1 / 2 ^ 15 ≤ realP := by
  have h := (ENNReal.toReal_le_toReal (by finiteness)
    TargetSum.acceptanceProbability_ne_top).mpr TargetSum.acceptanceProbability_lower.le
  rw [show (1 : ℝ) / 2 ^ 15 = 32768⁻¹ by norm_num]
  simpa [realP, ENNReal.toReal_div] using h

theorem ofReal_realP : ENNReal.ofReal realP = TargetSum.acceptanceProbability :=
  ENNReal.ofReal_toReal TargetSum.acceptanceProbability_ne_top

theorem hyp (q : ℕ) (hq : q + 1 ≤ 2 ^ 127) :
    Hyp realN realD realM realβ realP ((q : ℝ) + 1) where
  N_pos := by unfold realN; positivity
  D_le := by unfold realD realN; norm_num
  D_large := by unfold realD realN; norm_num
  M_pos := by unfold realM; positivity
  β_pos := by unfold realβ; positivity
  p_pos := realP_pos
  p_le := realP_le_one
  one_le := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  q_le := by
    unfold realN
    have : ((q + 1 : ℕ) : ℝ) ≤ ((2 ^ 127 : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast at this
    norm_num
    linarith

variable (q : ℕ) (parameter : PublicParameter)

/-- The per-epoch collision potential. -/
noncomputable def leafPotential (cache : QueryCache HashSpec) (leafIndex : LeafIndex) : ℝ :=
  leafMain realN realD realM realP ((q : ℝ) + 1)
      ((entries parameter cache leafIndex).ncard)
      ((validEntries parameter cache leafIndex).ncard)
      ((partneredEntries parameter cache leafIndex).ncard) +
    ∑ message : Message, msgTerm realD realβ realP ((q : ℝ) + 1)
      ((cachedRandomizersAt parameter leafIndex message cache).card)
      ((validRandomizers parameter cache leafIndex message).card)

/-- The rate per fresh query. -/
noncomputable def collisionRate : ℝ≥0∞ :=
  ENNReal.ofReal (rate realN realD realM realβ realP ((q : ℝ) + 1))

variable {q parameter}

theorem leafPotential_nonneg (hq : q + 1 ≤ 2 ^ 127) {cache : QueryCache HashSpec}
    {leafIndex : LeafIndex} (hK : (entries parameter cache leafIndex).ncard ≤ q + 1) :
    0 ≤ leafPotential q parameter cache leafIndex := by
  have h := hyp q hq
  unfold leafPotential
  refine add_nonneg (h.leafMain_nonneg ?_ (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun message _ => h.msgTerm_nonneg _ _)
  exact_mod_cast hK

theorem leafPotential_congr {cache cache' : QueryCache HashSpec} {leafIndex : LeafIndex}
    (h : ∀ entry, cache' (input parameter leafIndex entry) = cache (input parameter leafIndex entry)) :
    leafPotential q parameter cache' leafIndex = leafPotential q parameter cache leafIndex := by
  obtain ⟨hentries, hvalid, hpartnered, hcached, hvalidR⟩ := stats_congr h
  unfold leafPotential
  rw [hentries, hvalid, hpartnered,
    Finset.sum_congr rfl (fun message _ => by rw [hcached message, hvalidR message])]

theorem leafMain_C_add (K V C extra : ℝ) :
    leafMain realN realD realM realP ((q : ℝ) + 1) K V (C + extra) =
      leafMain realN realD realM realP ((q : ℝ) + 1) K V C + extra / (realP * realD) := by
  unfold leafMain
  rw [add_div]
  ring

theorem leafMain_C_mono {K V C C' : ℝ} (hC : C ≤ C') :
    leafMain realN realD realM realP ((q : ℝ) + 1) K V C ≤
      leafMain realN realD realM realP ((q : ℝ) + 1) K V C' := by
  have hpD : 0 < realP * realD := mul_pos realP_pos (by unfold realD; norm_num)
  unfold leafMain
  have := div_le_div_of_nonneg_right hC hpD.le
  linarith

/-! ### One fresh query at an epoch -/

theorem probEvent_uniform_mem (T : Set Digest) :
    Pr[fun output : Digest => output ∈ T | $ᵗ Digest] =
      (T.ncard : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  change Pr[(· ∈ T) | $ᵗ Digest] = _
  rw [probEvent_uniformSample]
  have hset : ((Finset.univ.filter fun digest : Digest => digest ∈ T : Finset Digest) :
      Set Digest) = T := by
    ext digest
    simp
  have hcard : ((Finset.univ.filter fun digest : Digest => digest ∈ T).card : ℝ≥0∞) =
      (T.ncard : ℝ≥0∞) := by
    rw [← Set.ncard_coe_finset, hset]
  have hdigest : (Fintype.card Digest : ℝ≥0∞) = ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
    rw [card_bitVec]
  rw [hcard, hdigest]

theorem tsum_uniform_ite (event : Digest → Prop) [DecidablePred event] (a b : ℝ≥0∞) :
    ∑' output, Pr[= output | $ᵗ Digest] * (if event output then a else b) =
      Pr[event | $ᵗ Digest] * a + Pr[fun output => ¬ event output | $ᵗ Digest] * b := by
  have hsplit : ∀ output, Pr[= output | $ᵗ Digest] * (if event output then a else b) =
      Pr[= output | $ᵗ Digest] * (if event output then a else 0) +
        Pr[= output | $ᵗ Digest] * (if ¬ event output then b else 0) := by
    intro output
    by_cases h : event output <;> simp [h]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_mul_right]
  congr 1 <;> refine tsum_congr fun output => ?_ <;> split_ifs <;> simp

theorem tsum_uniform_const (value : ℝ≥0∞) :
    ∑' output, Pr[= output | $ᵗ Digest] * value = value := by
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]

theorem probEvent_invalid_eq :
    Pr[fun output : Digest => ¬ Code.ValidDigest (output) | $ᵗ Digest] =
      ENNReal.ofReal (1 - realP) := by
  rw [Code.probEvent_invalidDigest_uniformHashOutput, code_acceptanceProbability,
    ENNReal.ofReal_sub _ realP_pos.le, ENNReal.ofReal_one, ofReal_realP]

theorem validDigest_of_mem_validDigests {cache : QueryCache HashSpec} {leafIndex : LeafIndex}
    {digest : Digest} (h : digest ∈ validDigests parameter cache leafIndex) :
    Code.ValidDigest digest := by
  obtain ⟨entry, hentry, hdigest⟩ := h
  obtain ⟨output, hcache, hvalid⟩ := mem_validEntries.mp hentry
  simp only [hcache, Option.getD_some] at hdigest
  rw [← hdigest]
  exact hvalid

/-- One fresh query at an epoch raises the expected potential by at most the rate. -/
theorem expected_leafPotential_cacheQuery_le (hq : q + 1 ≤ 2 ^ 127)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (fresh : Message × Randomness)
    (hfresh : cache (input parameter leafIndex fresh) = none)
    (hK : (entries parameter cache leafIndex).ncard + 1 ≤ q + 1) :
    ∑' output, Pr[= output | $ᵗ Digest] *
        ENNReal.ofReal (leafPotential q parameter
          (cache.cacheQuery (input parameter leafIndex fresh) output) leafIndex) ≤
      ENNReal.ofReal (leafPotential q parameter cache leafIndex) + collisionRate q := by
  classical
  have h := hyp q hq
  have hpD : 0 < realP * realD := mul_pos realP_pos (by unfold realD; norm_num)
  set K : ℝ := ((entries parameter cache leafIndex).ncard : ℝ)
  set V : ℝ := ((validEntries parameter cache leafIndex).ncard : ℝ)
  set C : ℝ := ((partneredEntries parameter cache leafIndex).ncard : ℝ)
  set n : ℝ := ((cachedRandomizersAt parameter leafIndex fresh.1 cache).card : ℝ)
  set v : ℝ := ((validRandomizers parameter cache leafIndex fresh.1).card : ℝ)
  set q' : ℝ := (q : ℝ) + 1
  let term : Message → QueryCache HashSpec → ℝ := fun message cache =>
    msgTerm realD realβ realP q' ((cachedRandomizersAt parameter leafIndex message cache).card)
      ((validRandomizers parameter cache leafIndex message).card)
  set R : ℝ := ∑ message ∈ Finset.univ.erase fresh.1, term message cache
  have hR : 0 ≤ R := Finset.sum_nonneg fun message _ => h.msgTerm_nonneg _ _
  have hsum : ∀ cache : QueryCache HashSpec, ∑ message : Message, term message cache =
      term fresh.1 cache + ∑ message ∈ Finset.univ.erase fresh.1, term message cache :=
    fun cache => (Finset.add_sum_erase _ _ (Finset.mem_univ fresh.1)).symm
  set A1 := leafMain realN realD realM realP q' (K + 1) (V + 1) C + msgTerm realD realβ realP q' (n + 1) (v + 1)
  set A0 := leafMain realN realD realM realP q' (K + 1) V C + msgTerm realD realβ realP q' (n + 1) v
  have hK' : K + 1 ≤ q' := by
    have : ((entries parameter cache leafIndex).ncard + 1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
      exact_mod_cast hK
    push_cast at this
    exact this
  have hV0 : 0 ≤ V := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hA1 : 0 ≤ A1 := add_nonneg (h.leafMain_nonneg hK' (by linarith) hC0)
    (h.msgTerm_nonneg _ _)
  have hA0 : 0 ≤ A0 := add_nonneg (h.leafMain_nonneg hK' hV0 hC0)
    (h.msgTerm_nonneg _ _)
  have hnotCached : fresh.2 ∉ cachedRandomizersAt parameter leafIndex fresh.1 cache := by
    simp only [cachedRandomizersAt, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact hfresh
  -- the potential after one output
  have hafter : ∀ output, leafPotential q parameter
      (cache.cacheQuery (input parameter leafIndex fresh) output) leafIndex ≤
        (if Code.ValidDigest (output) then A1 else A0) +
          (if output ∈ validDigests parameter cache leafIndex then
            2 / (realP * realD) else 0) + R := by
    intro output
    set cache' := cache.cacheQuery (input parameter leafIndex fresh) output
    have hKa : ((entries parameter cache' leafIndex).ncard : ℝ) = K + 1 := by
      rw [ncard_entries_cacheQuery fresh output hfresh]; push_cast; rfl
    have hVa := ncard_validEntries_cacheQuery fresh output hfresh
    have hCa := ncard_partneredEntries_cacheQuery_le fresh output hfresh
    have hna : ((cachedRandomizersAt parameter leafIndex fresh.1 cache').card : ℝ) = n + 1 := by
      have hcq : cachedRandomizersAt parameter leafIndex fresh.1 cache' =
          insert fresh.2 (cachedRandomizersAt parameter leafIndex fresh.1 cache) :=
        cachedRandomizersAt_cacheQuery parameter leafIndex fresh.1 cache fresh.2 output
      rw [hcq, Finset.card_insert_of_notMem hnotCached]
      push_cast; rfl
    have hva := card_validRandomizers_cacheQuery_self fresh output hfresh
    have hrest : ∑ message ∈ Finset.univ.erase fresh.1, term message cache' = R := by
      apply Finset.sum_congr rfl
      intro message hmessage
      have hne := Finset.ne_of_mem_erase hmessage
      simp only [term, cache', cachedRandomizersAt_cacheQuery_other fresh output hfresh hne,
        validRandomizers_cacheQuery_other fresh output hfresh hne]
    unfold leafPotential
    rw [hsum cache', hrest, hKa, hVa]
    simp only [term]
    rw [hna, hva]
    have hhitValid : output ∈ validDigests parameter cache leafIndex →
        Code.ValidDigest (output) := validDigest_of_mem_validDigests
    by_cases hvalid : Code.ValidDigest (output)
    · simp only [hvalid, if_true]
      by_cases hhit : output ∈ validDigests parameter cache leafIndex
      · simp only [hhit, if_true] at hCa ⊢
        have := leafMain_C_mono (q := q) (K := K + 1) (V := V + 1) hCa
        rw [leafMain_C_add] at this
        linarith
      · simp only [hhit, if_false, add_zero] at hCa ⊢
        have := leafMain_C_mono (q := q) (K := K + 1) (V := V + 1) hCa
        linarith
    · have hhit : output ∉ validDigests parameter cache leafIndex :=
        fun hmem => hvalid (hhitValid hmem)
      simp only [hvalid, hhit, if_false, add_zero] at hCa ⊢
      have := leafMain_C_mono (q := q) (K := K + 1) (V := V) hCa
      linarith
  -- the expectation of the bound
  set hitProb : ℝ≥0∞ := Pr[fun output : Digest =>
    output ∈ validDigests parameter cache leafIndex | $ᵗ Digest]
  have hhitProb : hitProb = ENNReal.ofReal
      ((validDigests parameter cache leafIndex).ncard / realN) := by
    simp only [hitProb]
    rw [probEvent_uniform_mem, ENNReal.ofReal_div_of_pos (by unfold realN; positivity)]
    simp [realN, digestBits]
    norm_num
  have hhitReal : (validDigests parameter cache leafIndex).ncard / realN ≤ V / realN := by
    apply div_le_div_of_nonneg_right _ (by unfold realN; positivity)
    show ((validDigests parameter cache leafIndex).ncard : ℝ) ≤
      ((validEntries parameter cache leafIndex).ncard : ℝ)
    exact_mod_cast ncard_validDigests_le (parameter := parameter) (cache := cache)
      (leafIndex := leafIndex)
  calc
    _ ≤ ∑' output, Pr[= output | $ᵗ Digest] *
          ((if Code.ValidDigest (output) then ENNReal.ofReal A1
              else ENNReal.ofReal A0) +
            (if output ∈ validDigests parameter cache leafIndex then
              ENNReal.ofReal (2 / (realP * realD)) else 0) + ENNReal.ofReal R) := by
      refine ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl ?_
      refine (ENNReal.ofReal_le_ofReal (hafter output)).trans ?_
      refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
      refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ ?_)
      · split_ifs <;> exact le_rfl
      · split_ifs <;> simp
    _ = TargetSum.acceptanceProbability * ENNReal.ofReal A1 +
          ENNReal.ofReal (1 - realP) * ENNReal.ofReal A0 +
          hitProb * ENNReal.ofReal (2 / (realP * realD)) + ENNReal.ofReal R := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_uniform_ite, tsum_uniform_ite,
        tsum_uniform_const, TargetSum.probEvent_validDigest_uniform, probEvent_invalid_eq]
      have hzero : Pr[fun output : Digest =>
          ¬ output ∈ validDigests parameter cache leafIndex | $ᵗ Digest] * 0 = 0 :=
        mul_zero _
      rw [hzero, add_zero]
    _ = ENNReal.ofReal (realP * A1 + (1 - realP) * A0 +
          (validDigests parameter cache leafIndex).ncard / realN * (2 / (realP * realD)) + R) := by
      have hN : 0 < realN := by unfold realN; positivity
      have hhit0 : 0 ≤ ((validDigests parameter cache leafIndex).ncard : ℝ) / realN :=
        div_nonneg (Nat.cast_nonneg _) hN.le
      have h1p : 0 ≤ 1 - realP := by linarith [realP_le_one]
      have ht1 : 0 ≤ realP * A1 := mul_nonneg realP_pos.le hA1
      have ht2 : 0 ≤ (1 - realP) * A0 := mul_nonneg h1p hA0
      have ht3 : 0 ≤ ((validDigests parameter cache leafIndex).ncard : ℝ) / realN *
          (2 / (realP * realD)) := mul_nonneg hhit0 (div_nonneg (by norm_num) hpD.le)
      rw [← ofReal_realP, hhitProb, ← ENNReal.ofReal_mul realP_pos.le,
        ← ENNReal.ofReal_mul h1p, ← ENNReal.ofReal_mul hhit0,
        ← ENNReal.ofReal_add ht1 ht2, ← ENNReal.ofReal_add (add_nonneg ht1 ht2) ht3,
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg ht1 ht2) ht3) hR]
    _ ≤ ENNReal.ofReal (leafMain realN realD realM realP q' K V C +
          msgTerm realD realβ realP q' n v + rate realN realD realM realβ realP q' + R) := by
      apply ENNReal.ofReal_le_ofReal
      have hdrift := leaf_drift_le h (K := K) (V := V) (C := C) (n := n) (v := v)
        (hit := (validDigests parameter cache leafIndex).ncard / realN) hK'
        (by
          show ((cachedRandomizersAt parameter leafIndex fresh.1 cache).card : ℝ) ≤
            ((entries parameter cache leafIndex).ncard : ℝ)
          exact_mod_cast card_cachedRandomizersAt_le_ncard_entries (parameter := parameter)
            (cache := cache) (leafIndex := leafIndex) fresh.1) hn0
        (div_nonneg (Nat.cast_nonneg _) (by unfold realN; positivity)) hhitReal
      change _ + realP * A1 + (1 - realP) * A0 ≤ _ at hdrift
      linarith
    _ ≤ ENNReal.ofReal (leafPotential q parameter cache leafIndex) + collisionRate q := by
      have hpot : leafPotential q parameter cache leafIndex =
          leafMain realN realD realM realP q' K V C + msgTerm realD realβ realP q' n v + R := by
        unfold leafPotential
        rw [hsum cache]
        simp only [term]
        ring
      rw [hpot, collisionRate]
      refine (ENNReal.ofReal_le_ofReal (le_of_eq (by ring))).trans ENNReal.ofReal_add_le

end XmssSecurity.TargetSum.Direct.Collision

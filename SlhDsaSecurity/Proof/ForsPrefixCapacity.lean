import SlhDsaSecurity.Proof.ForsConcentrationOccupancy
import Mathlib.Probability.Independence.Basic

/-!
# Simultaneous prefix capacity for a fixed disclosure tape

These probability lemmas concern independent leaf samples with fixed instance
assignments. They do not identify an adaptive shared-oracle transcript with that
distribution.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace SlhDsaSecurity.ForsPrefixCapacity

/-- A deliberately loose factorial-moment bound, sufficient for the prefix cap. -/
theorem independent_count_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (events : ι → Set Ω) (hind : iIndepSet events μ) (r : Nat) :
    μ {ω | r ≤ (Finset.univ.filter (fun i => ω ∈ events i)).card} ≤
      (∑ i, μ (events i)) ^ r := by
  let selected : (Fin r → ι) → Set Ω := fun f =>
    if Function.Injective f then ⋂ j, events (f j) else ∅
  have hcover : {ω | r ≤ (Finset.univ.filter (fun i => ω ∈ events i)).card} ⊆
      ⋃ f, selected f := by
    intro ω hω
    let S := {i : ι // ω ∈ events i}
    have hcard : r ≤ Fintype.card S := by
      simpa only [S, Fintype.card_subtype, Set.mem_setOf_eq] using hω
    let choose : Fin r → S := fun j =>
      (Fintype.equivFin S).symm ⟨j.val, lt_of_lt_of_le j.isLt hcard⟩
    let f : Fin r → ι := fun j => (choose j).val
    have hf : Function.Injective f := by
      intro a b hab
      have hab' : choose a = choose b := Subtype.ext hab
      have hh := congrArg (Fintype.equivFin S) hab'
      simpa only [choose, Equiv.apply_symm_apply, Fin.mk.injEq, Fin.ext_iff] using hh
    exact Set.mem_iUnion.mpr ⟨f, by simpa [selected, hf] using fun j => (choose j).property⟩
  calc
    _ ≤ μ (⋃ f, selected f) := measure_mono hcover
    _ ≤ ∑ f, μ (selected f) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ f : Fin r → ι, ∏ j, μ (events (f j)) := by
      apply Finset.sum_le_sum
      intro f _
      by_cases hf : Function.Injective f
      · have h := (hind.precomp hf).meas_biInter Finset.univ
        simpa [selected, hf] using h.le
      · simp [selected, hf]
    _ = _ := by rw [Fintype.sum_pow]

noncomputable section

abbrev Leaf := Fin 4096
abbrev Prefix := Fin 10 → Leaf
abbrev TreeTape (requests : Nat) := Fin requests → Leaf
abbrev InstanceTape (requests : Nat) := Fin 10 → TreeTape requests
abbrev Tape {ι : Type*} (loads : ι → Nat) := (i : ι) → InstanceTape (loads i)

def leafMeasure : Measure Leaf := (PMF.uniformOfFintype Leaf).toMeasure
def treeMeasure (requests : Nat) : Measure (TreeTape requests) :=
  Measure.pi (fun _ => leafMeasure)
def instanceMeasure (requests : Nat) : Measure (InstanceTape requests) :=
  Measure.pi (fun _ => treeMeasure requests)
def tapeMeasure {ι : Type*} [Fintype ι] (loads : ι → Nat) : Measure (Tape loads) :=
  Measure.pi (fun i => instanceMeasure (loads i))

instance : IsProbabilityMeasure leafMeasure := by unfold leafMeasure; infer_instance
instance (n : Nat) : IsProbabilityMeasure (treeMeasure n) := by
  unfold treeMeasure; infer_instance
instance (n : Nat) : IsProbabilityMeasure (instanceMeasure n) := by
  unfold instanceMeasure; infer_instance
instance {ι : Type*} [Fintype ι] (loads : ι → Nat) :
    IsProbabilityMeasure (tapeMeasure loads) := by unfold tapeMeasure; infer_instance

def TreeCovered {requests : Nat} (leaf : Leaf) (tape : TreeTape requests) : Prop :=
  ∃ j, tape j = leaf
def PrefixCovered {requests : Nat} (target : Prefix) (tape : InstanceTape requests) : Prop :=
  ∀ tree, TreeCovered (target tree) (tape tree)

theorem product_event_probability {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (event : Set (Ω i)) (hm : MeasurableSet event) :
    Measure.pi μ {ω | ω i ∈ event} = μ i event := by
  have h := congrArg (fun ν : Measure (Ω i) => ν event) (measurePreserving_eval μ i).map_eq
  rw [Measure.map_apply (measurable_pi_apply i) hm] at h
  exact h

theorem tree_covered_probability (requests : Nat) (leaf : Leaf) :
    treeMeasure requests {tape | TreeCovered leaf tape} ≤ (requests : ℝ≥0∞) / 4096 := by
  have heq : {tape : TreeTape requests | TreeCovered leaf tape} =
      ⋃ j : Fin requests, {tape | tape j = leaf} := by ext tape; simp [TreeCovered]
  rw [heq]
  calc
    _ ≤ ∑ j : Fin requests, treeMeasure requests {tape | tape j = leaf} :=
      measure_iUnion_fintype_le _ _
    _ = _ := by
      have h (j : Fin requests) : treeMeasure requests {tape | tape j = leaf} =
          (4096 : ℝ≥0∞)⁻¹ := by
        change Measure.pi (fun _ : Fin requests => leafMeasure)
          {tape | tape j ∈ ({leaf} : Set Leaf)} = _
        rw [product_event_probability _ _ _ (measurableSet_singleton _)]
        simp [leafMeasure, PMF.uniformOfFintype_apply, Leaf]
      simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        div_eq_mul_inv]

theorem prefix_covered_probability (requests : Nat) (target : Prefix) :
    instanceMeasure requests {tape | PrefixCovered target tape} ≤
      (requests : ℝ≥0∞) ^ 10 / 2 ^ 120 := by
  have heq : {tape : InstanceTape requests | PrefixCovered target tape} =
      Set.univ.pi (fun tree => {tape | TreeCovered (target tree) tape}) := by
    ext tape; simp [PrefixCovered]
  rw [heq, instanceMeasure, Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin 10, (requests : ℝ≥0∞) / 4096 :=
      Finset.prod_le_prod' (fun tree _ => tree_covered_probability requests (target tree))
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat, div_pow]
      norm_num

theorem prefix_instances_independent {ι : Type*} [Fintype ι] (loads : ι → Nat)
    (target : Prefix) :
    iIndepSet (fun i => {tape : Tape loads | PrefixCovered target (tape i)})
      (tapeMeasure loads) := by
  apply (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)).2
  intro s
  have heq : (⋂ i ∈ s, {tape : Tape loads | PrefixCovered target (tape i)}) =
      (s : Set ι).pi (fun i => {tape | PrefixCovered target tape}) := by
    ext tape; simp
  rw [heq, tapeMeasure, Measure.pi_pi_finset]
  apply Finset.prod_congr rfl
  intro i _
  exact (product_event_probability (fun j => instanceMeasure (loads j)) i
    {tape | PrefixCovered target tape} MeasurableSet.of_discrete).symm

def eligibleCount {ι : Type*} [Fintype ι] {loads : ι → Nat}
    (target : Prefix) (tape : Tape loads) : Nat :=
  (Finset.univ.filter (fun i => PrefixCovered target (tape i))).card

theorem prefix_probability_sum {ι : Type*} [Fintype ι] (loads : ι → Nat)
    (hload : ∑ i, loads i ^ 14 ≤ 2 ^ 103) (target : Prefix) :
    (∑ i, tapeMeasure loads {tape | PrefixCovered target (tape i)}) ≤
      (1 : ℝ≥0∞) / 2 ^ 17 := by
  have hsmall : ∑ i, loads i ^ 10 ≤ 2 ^ 103 := by
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans hload
    by_cases hz : loads i = 0
    · simp [hz]
    · exact pow_le_pow_right' (Nat.one_le_iff_ne_zero.mpr hz) (by decide)
  have hcast : (∑ i, (loads i : ℝ≥0∞) ^ 10) ≤ 2 ^ 103 := by
    exact_mod_cast hsmall
  calc
    _ ≤ ∑ i, (loads i : ℝ≥0∞) ^ 10 / 2 ^ 120 := by
      apply Finset.sum_le_sum
      intro i _
      have h := product_event_probability (fun j => instanceMeasure (loads j)) i
        {tape | PrefixCovered target tape} MeasurableSet.of_discrete
      exact h.trans_le (prefix_covered_probability (loads i) target)
    _ = (∑ i, (loads i : ℝ≥0∞) ^ 10) / 2 ^ 120 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ 2 ^ 103 / 2 ^ 120 := ENNReal.div_le_div_right hcast _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

/-- For one fixed 120-bit prefix, sixteen eligible instances occur with
probability at most `2^-272`. -/
theorem fixed_prefix_tail {ι : Type*} [Fintype ι] (loads : ι → Nat)
    (hload : ∑ i, loads i ^ 14 ≤ 2 ^ 103) (target : Prefix) :
    tapeMeasure loads {tape | 16 ≤ eligibleCount target tape} ≤
      (1 : ℝ≥0∞) / 2 ^ 272 := by
  calc
    _ ≤ (∑ i, tapeMeasure loads {tape | PrefixCovered target (tape i)}) ^ 16 :=
      independent_count_tail _ _ (prefix_instances_independent loads target) 16
    _ ≤ ((1 : ℝ≥0∞) / 2 ^ 17) ^ 16 :=
      pow_le_pow_left' (prefix_probability_sum loads hload target) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
      rw [show (272 : Nat) = 136 + 136 by decide, pow_add]
      norm_num

/-- Except with probability `2^-152`, every 120-bit prefix is compatible with
the disclosures at at most fifteen instances, simultaneously. The assignments
are fixed; all leaf coordinates in `tapeMeasure` are independent uniform samples. -/
theorem simultaneous_prefix_cap {ι : Type*} [Fintype ι] (loads : ι → Nat)
    (hload : ∑ i, loads i ^ 14 ≤ 2 ^ 103) :
    tapeMeasure loads {tape | ∃ target : Prefix, 16 ≤ eligibleCount target tape} ≤
      (1 : ℝ≥0∞) / 2 ^ 152 := by
  have heq : {tape : Tape loads | ∃ target : Prefix, 16 ≤ eligibleCount target tape} =
      ⋃ target : Prefix, {tape | 16 ≤ eligibleCount target tape} := by ext tape; simp
  rw [heq]
  calc
    _ ≤ ∑ target : Prefix, tapeMeasure loads {tape | 16 ≤ eligibleCount target tape} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Prefix, (1 : ℝ≥0∞) / 2 ^ 272 :=
      Finset.sum_le_sum (fun target _ => fixed_prefix_tail loads hload target)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Prefix,
        Fintype.card_fun, Fintype.card_fin, Leaf]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
      rw [show (272 : Nat) = 136 + 136 by decide, pow_add]
      norm_num

end

end SlhDsaSecurity.ForsPrefixCapacity

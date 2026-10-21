import SlhDsaSecurity.Proof.ForsDisclosureTape

/-!
# Prefix capacity for a uniform full-view disclosure tape

Conditioning fixes the instance word, and an injective coordinate projection
reindexes the first ten leaf coordinates into the product law used by the prefix
cap. This is still an iid-tape result, not an adaptive random-oracle coupling.
-/

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SlhDsaSecurity.ForsDisclosurePrefix

open ForsDisclosureTape

abbrev Prefix := ForsPrefixCapacity.Prefix

def firstTree (tree : Fin 10) : Tree := ⟨tree.val, by have := tree.isLt; change _ < 14; omega⟩

def wordLoads {requests : Nat} (word : InstanceWord requests) : Instance → Nat :=
  ForsConcentration.wordLoads word

theorem wordLoads_eq_card {requests : Nat} (word : InstanceWord requests) (i : Instance) :
    wordLoads word i = (Finset.univ.filter (fun j => word j = i)).card := by
  simp only [wordLoads, ForsConcentration.wordLoads, ForsConcentration.wordCounts,
    Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_eq_sum_ones, Finset.sum_filter]

def fiberEquiv {requests : Nat} (word : InstanceWord requests) (i : Instance) :
    {j : Fin requests // word j = i} ≃ Fin (wordLoads word i) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype, wordLoads_eq_card])

abbrev Coordinates {requests : Nat} (word : InstanceWord requests) :=
  (i : Instance) × (Fin 10 × Fin (wordLoads word i))

def coordinate {requests : Nat} (word : InstanceWord requests) (c : Coordinates word) :
    Fin requests × Tree := ((fiberEquiv word c.1).symm c.2.2, firstTree c.2.1)

theorem coordinate_injective {requests : Nat} (word : InstanceWord requests) :
    Function.Injective (coordinate word) := by
  rintro ⟨i, tree, occurrence⟩ ⟨i', tree', occurrence'⟩ h
  have hj := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  change ((fiberEquiv word i).symm occurrence).val =
    ((fiberEquiv word i').symm occurrence').val at hj
  have hi : i = i' := ((fiberEquiv word i).symm occurrence).property.symm.trans
    ((congrArg word hj).trans ((fiberEquiv word i').symm occurrence').property)
  subst i'
  have ho : occurrence = occurrence' := (fiberEquiv word i).symm.injective (Subtype.ext hj)
  have htree : tree = tree' := Fin.ext (congrArg (fun t : Tree => t.val) ht)
  subst occurrence'
  subst tree'
  rfl

def flatEquiv (requests : Nat) : ((Fin requests × Tree) → Leaf) ≃ LeafWord requests where
  toFun flat j tree := flat (j, tree)
  invFun leaves pair := leaves pair.1 pair.2
  left_inv := by intro flat; rfl
  right_inv := by intro leaves; rfl

def groupedEquiv {requests : Nat} (word : InstanceWord requests) :
    (Coordinates word → Leaf) ≃ ForsPrefixCapacity.Tape (wordLoads word) where
  toFun flat i tree occurrence := flat ⟨i, tree, occurrence⟩
  invFun grouped c := grouped c.1 c.2.1 c.2.2
  left_inv := by intro flat; rfl
  right_inv := by intro grouped; rfl

def groupLeaves {requests : Nat} (word : InstanceWord requests) (leaves : LeafWord requests) :
    ForsPrefixCapacity.Tape (wordLoads word) :=
  fun i tree occurrence => leaves ((fiberEquiv word i).symm occurrence) (firstTree tree)

local instance {requests : Nat} (word : InstanceWord requests) :
    SampleableType (ForsPrefixCapacity.Tape (wordLoads word)) := SampleableType.ofFintype _

theorem evalDist_groupLeaves_uniform {requests : Nat} (word : InstanceWord requests) :
    𝒟[groupLeaves word <$> ($ᵗ LeafWord requests : ProbComp (LeafWord requests))] =
      𝒟[($ᵗ ForsPrefixCapacity.Tape (wordLoads word) :
        ProbComp (ForsPrefixCapacity.Tape (wordLoads word)))] := by
  have hflat := evalDist_map_bijective_uniform_cross (α := (Fin requests × Tree) → Leaf)
    (flatEquiv requests) (flatEquiv requests).bijective
  have hcoord := evalDist_uniformSample_map_comp_injective
    (R := Leaf) (coordinate_injective word)
  have hgroup := evalDist_map_bijective_uniform_cross (α := Coordinates word → Leaf)
    (groupedEquiv word) (groupedEquiv word).bijective
  rw [evalDist_map, ← hflat, ← evalDist_map]
  rw [show groupLeaves word <$> (flatEquiv requests <$> ($ᵗ ((Fin requests × Tree) → Leaf))) =
      groupedEquiv word <$> ((fun flat => flat ∘ coordinate word) <$>
        ($ᵗ ((Fin requests × Tree) → Leaf))) by
          simp only [Functor.map_map]; rfl]
  rw [evalDist_map, show 𝒟[(fun flat => flat ∘ coordinate word) <$>
      ($ᵗ ((Fin requests × Tree) → Leaf))] = 𝒟[$ᵗ (Coordinates word → Leaf)] by
        simpa only [bind_pure_comp] using hcoord, ← evalDist_map]
  exact hgroup

theorem uniform_pi_measure {ι : Type} [Fintype ι] {α : ι → Type}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, DiscreteMeasurableSpace (α i)] :
    (PMF.uniformOfFintype ((i : ι) → α i)).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (α i)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

set_option maxRecDepth 10000 in
theorem prefix_tape_uniform_measure (counts : Instance → Nat) :
    (PMF.uniformOfFintype (ForsPrefixCapacity.Tape counts)).toMeasure =
      ForsPrefixCapacity.tapeMeasure counts := by
  apply Measure.ext_of_singleton
  intro grouped
  simp only [ForsPrefixCapacity.tapeMeasure, ForsPrefixCapacity.instanceMeasure,
    ForsPrefixCapacity.treeMeasure, Measure.pi_singleton, ForsPrefixCapacity.leafMeasure,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFintype_apply]
  simp only [ForsPrefixCapacity.Tape, ForsPrefixCapacity.InstanceTape,
    ForsPrefixCapacity.TreeTape, Fintype.card_pi, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib (f := fun i : Instance =>
    ∏ _ : Fin 10, ∏ _ : Fin (counts i), (Fintype.card ForsPrefixCapacity.Leaf : ℝ≥0∞))
    (fun _ _ _ _ _ => Or.inr (ENNReal.prod_ne_top (fun _ _ =>
      ENNReal.prod_ne_top (fun _ _ => ENNReal.natCast_ne_top _))))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ENNReal.prod_inv_distrib (f := fun _ : Fin 10 =>
    ∏ _ : Fin (counts i), (Fintype.card ForsPrefixCapacity.Leaf : ℝ≥0∞))
    (fun _ _ _ _ _ => Or.inr (ENNReal.prod_ne_top (fun _ _ => ENNReal.natCast_ne_top _)))]
  apply Finset.prod_congr rfl
  intro tree _
  exact ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))

def joinedTape {requests : Nat} (word : InstanceWord requests) (leaves : LeafWord requests) :
    Tape requests := fun j => (word j, leaves j)

def PrefixEligible (revealed : ForsCoverage.Disclosures) (target : Prefix) (i : Instance) : Prop :=
  ∀ tree : Fin 10, target tree ∈ revealed i (firstTree tree)

def BadPrefix (revealed : ForsCoverage.Disclosures) : Prop :=
  ∃ target : Prefix, 16 ≤ (Finset.univ.filter (PrefixEligible revealed target)).card

theorem groupLeaves_covered_iff {requests : Nat} (word : InstanceWord requests)
    (leaves : LeafWord requests) (target : Prefix) (i : Instance) :
    ForsPrefixCapacity.PrefixCovered target (groupLeaves word leaves i) ↔
      PrefixEligible (disclosures (joinedTape word leaves)) target i := by
  constructor
  · intro h tree
    obtain ⟨occurrence, hleaf⟩ := h tree
    apply Finset.mem_image.mpr
    refine ⟨(fiberEquiv word i).symm occurrence, ?_, hleaf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((fiberEquiv word i).symm occurrence).property⟩
  · intro h tree
    obtain ⟨j, hj, hleaf⟩ := Finset.mem_image.mp (h tree)
    have hj' : word j = i := (Finset.mem_filter.mp hj).2
    refine ⟨fiberEquiv word i ⟨j, hj'⟩, ?_⟩
    simpa only [groupLeaves, Equiv.symm_apply_apply, joinedTape] using hleaf

theorem fixed_assignment_prefix_cap {requests : Nat} (word : InstanceWord requests)
    (hload : ∑ i, wordLoads word i ^ 14 ≤ 2 ^ 103) :
    Pr[fun leaves => BadPrefix (disclosures (joinedTape word leaves)) |
      ($ᵗ LeafWord requests : ProbComp (LeafWord requests))] ≤ (1 : ℝ≥0∞) / 2 ^ 152 := by
  have hevent : (fun leaves : LeafWord requests => BadPrefix (disclosures (joinedTape word leaves))) =
      (fun grouped => ∃ target : Prefix,
        16 ≤ ForsPrefixCapacity.eligibleCount target grouped) ∘ groupLeaves word := by
    funext leaves
    simp only [BadPrefix, Function.comp_apply, ForsPrefixCapacity.eligibleCount,
      groupLeaves_covered_iff]
  rw [hevent, ← probEvent_map,
    probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_groupLeaves_uniform word),
    uniform_prob_eq_measure, prefix_tape_uniform_measure]
  exact ForsPrefixCapacity.simultaneous_prefix_cap (wordLoads word) hload

theorem evalDist_uniform_pair {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    𝒟[(do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b) : ProbComp (α × β))] =
      𝒟[($ᵗ (α × β) : ProbComp (α × β))] := by
  have hpair : (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b) : ProbComp (α × β)) =
      Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) := by simp [monad_norm]
  rw [hpair]
  apply evalDist_ext
  intro pair
  simp only [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    Fintype.card_prod, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

theorem evalDist_joinedTape_uniform (requests : Nat) :
    𝒟[(do let word ← $ᵗ InstanceWord requests
          let leaves ← $ᵗ LeafWord requests
          pure (joinedTape word leaves) : ProbComp (Tape requests))] =
      𝒟[($ᵗ Tape requests : ProbComp (Tape requests))] := by
  have hjoin : (do
      let word ← $ᵗ InstanceWord requests
      let leaves ← $ᵗ LeafWord requests
      pure (joinedTape word leaves) : ProbComp (Tape requests)) =
      (splitTape requests).symm <$>
        (do let word ← $ᵗ InstanceWord requests
            let leaves ← $ᵗ LeafWord requests
            pure (word, leaves)) := by
    simp only [monad_norm, splitTape]
    rfl
  rw [hjoin, evalDist_map, evalDist_uniform_pair, ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross
    (α := InstanceWord requests × LeafWord requests)
    (splitTape requests).symm (splitTape requests).symm.bijective

/-- The simultaneous prefix cap for the actual full-view iid tape, including
the single global load exception. -/
theorem bad_prefix_probability (requests : Nat) (hrequests : requests ≤ 5 * 2 ^ 62) :
    Pr[fun tape => BadPrefix (disclosures tape) |
      ($ᵗ Tape requests : ProbComp (Tape requests))] ≤
        (1 : ℝ≥0∞) / 2 ^ 141 + (1 : ℝ≥0∞) / 2 ^ 152 := by
  have hloads : Pr[fun word : InstanceWord requests => ¬ (∑ i, wordLoads word i ^ 14 ≤ 2 ^ 103) |
      ($ᵗ InstanceWord requests : ProbComp (InstanceWord requests))] ≤
        (1 : ℝ≥0∞) / 2 ^ 141 := by
    have h := bad_load_probability requests hrequests
    simp_rw [loads_eq_wordLoads] at h
    rw [show (fun tape : Tape requests =>
        2 ^ 103 < ∑ i, ForsConcentration.wordLoads (instanceWord tape) i ^ 14) =
        (fun word => 2 ^ 103 < ∑ i, wordLoads word i ^ 14) ∘ instanceWord from rfl,
      ← probEvent_map,
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_instanceWord_uniform requests)] at h
    simpa only [Nat.not_le] using h
  have h := probEvent_bind_le_add
    (mx := ($ᵗ InstanceWord requests : ProbComp (InstanceWord requests)))
    (my := fun word => joinedTape word <$> ($ᵗ LeafWord requests))
    (p := fun word => ∑ i, wordLoads word i ^ 14 ≤ 2 ^ 103)
    (q := fun tape => ¬ BadPrefix (disclosures tape)) hloads
    (fun word _ hword => by
      rw [probEvent_map]
      simpa only [Function.comp_def, not_not] using fixed_assignment_prefix_cap word hword)
  have hdist := evalDist_joinedTape_uniform requests
  simp only [bind_pure_comp] at hdist
  simpa only [not_not, probEvent_congr' (fun _ _ => Iff.rfl) hdist] using h

end SlhDsaSecurity.ForsDisclosurePrefix

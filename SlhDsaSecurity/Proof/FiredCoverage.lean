import SlhDsaSecurity.Proof.NoticingTape
import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.ForsConcentrationSharper

/-!
# Coverage when a served target may also disclose

`BlockViews.prob_targetCovered_le` charges a target digest covered by the **disclosing block**.
The game's coverage event is wider in exactly one way: a digest the adversary queried *before*
the signer asked for it is filed as a target, and if a later signature serves it, it discloses
too. Ruling that out costs one unit of `2 ^ -128` per message-class query — the ordering
defect — and the ledger has no unit to spare for it, because the same query is already a coverage
target and a guess at `SK.prf`.

This file charges the wider event instead. A target cell `t` is covered by the disclosing block
together with the target cells that **fired**: cells whose input a later signature served. The
charge is

    Pr[¬ good block] + E[length] · 2 ^ -129 + E[length] · rightLength · 2 ^ -303,

so at any `rightLength ≤ 2 ^ 128` the fired cells cost a sliver of the half unit the sharper
load cap (`2 ^ 102`) leaves free.

**Why the fired cells are cheap.** The covering witnesses for `t` that are themselves target cells
all sit at `t`'s own FORS instance. If there are none, `t` is covered by the block — the first-order
term. If there is exactly one, `j`, then `t` is covered by the block together with `j`'s view
(`HelpedBy`), and two facts multiply: `j` fired, which a fresh `PRF_msg` draw decides at
`2 ^ -128` (`hthin1`), and two independent uniform views at one instance cover each other's leaves
with probability at most `2 ^ -177` (`prob_helpedBy_le`). If there are two, two fired cells share an
instance: `2 ^ -256` for the two draws (`hthin2`) and `2 ^ -63` for the instance.

**What the run has to supply** is the two thinning bounds and one causality fact, all stated per
pair of blocks so they are facts about the run rather than about the blocks' law:

* `hcausal` — whether the run reaches target cell `index` does not depend on any cell at or after
  it. `NoticingTape.prob_selected_hit_le_of_causal` needs only `cell = index`; the pairs here also
  need later cells, because the helper may be read after the target was reached.
* `hthin1`, `hthin2` — reaching a cell and then seeing it fire costs `2 ^ -128` per cell.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FiredCoverage

open DigestTape NoticingTape BlockViews ForsCoverage

/-! ## Two views at one instance -/

/-- **A target covered by the disclosures together with one helper view at its own instance.** -/
def HelpedBy (revealed : Disclosures) (target helper : View) : Prop :=
  helper.1 = target.1 ∧
    ∀ tree, target.2 tree ∈ revealed target.1 tree ∨ helper.2 tree = target.2 tree

instance (revealed : Disclosures) (target helper : View) :
    Decidable (HelpedBy revealed target helper) := by
  unfold HelpedBy
  infer_instance

/-- The leaf pairs one tree contributes: the target's leaf disclosed, or the helper's equal. -/
def LeafPairs (shown : Finset Leaf) : Type :=
  {pair : Leaf × Leaf // pair.1 ∈ shown ∨ pair.2 = pair.1}

instance (shown : Finset Leaf) : Fintype (LeafPairs shown) := by
  unfold LeafPairs
  infer_instance

/-- The helped pairs, as a dependent choice of instance and per-tree leaf pairs. -/
def helpedEquiv (revealed : Disclosures) :
    (Σ index : Instance, (tree : Tree) → LeafPairs (revealed index tree)) ≃
      {pair : View × View // HelpedBy revealed pair.1 pair.2} where
  toFun choice := ⟨((choice.1, fun tree => (choice.2 tree).val.1),
      (choice.1, fun tree => (choice.2 tree).val.2)),
    rfl, fun tree => (choice.2 tree).property⟩
  invFun pair := ⟨pair.val.1.1, fun tree =>
    ⟨(pair.val.1.2 tree, pair.val.2.2 tree), by
      rcases pair.property.2 tree with hshown | hsame
      · exact Or.inl hshown
      · exact Or.inr hsame⟩⟩
  left_inv := by rintro ⟨index, leaves⟩; rfl
  right_inv := by
    rintro ⟨⟨⟨index, targetLeaves⟩, ⟨helperIndex, helperLeaves⟩⟩, hindex, htrees⟩
    simp only at hindex
    subst hindex
    rfl

set_option linter.constructorNameAsVariable false in
/-- Pairs at one tree: every leaf of the shown set with any helper leaf, and every other leaf with
an equal helper leaf. -/
theorem card_leafPairs_le (shown : Finset Leaf) :
    Fintype.card (LeafPairs shown) ≤ 2 ^ 12 * (shown.card + 1) := by
  classical
  unfold LeafPairs
  rw [Fintype.card_subtype]
  have hsplit : (Finset.univ.filter fun pair : Leaf × Leaf => pair.1 ∈ shown ∨ pair.2 = pair.1) ⊆
      (shown ×ˢ (Finset.univ : Finset Leaf)) ∪
        (Finset.univ.image fun leaf : Leaf => (leaf, leaf)) := by
    intro pair hpair
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpair
    rcases hpair with hshown | hsame
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hshown, Finset.mem_univ _⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨pair.1, Finset.mem_univ _, ?_⟩)
      exact Prod.ext rfl hsame.symm
  refine le_trans (Finset.card_le_card hsplit) (le_trans (Finset.card_union_le _ _) ?_)
  rw [Finset.card_product, Finset.card_univ]
  refine le_trans (Nat.add_le_add_left Finset.card_image_le _) ?_
  have hleaf : Fintype.card Leaf = 2 ^ 12 := by
    unfold ForsCoverage.Leaf MessageDigest.ForsLeaf forsHeight; exact Fintype.card_fin _
  rw [Finset.card_univ, hleaf, mul_add, mul_one, mul_comm]

/-- **The count of helped pairs.** -/
theorem card_helped_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index) :
    (Finset.univ.filter fun pair : View × View => HelpedBy revealed pair.1 pair.2).card ≤
      ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_congr (helpedEquiv revealed), Fintype.card_sigma]
  refine Finset.sum_le_sum fun index _ => ?_
  rw [Fintype.card_pi]
  calc ∏ tree : Tree, Fintype.card (LeafPairs (revealed index tree))
      ≤ ∏ _tree : Tree, 2 ^ 12 * (loads index + 1) :=
        Finset.prod_le_prod' fun tree _ =>
          le_trans (card_leafPairs_le _) (Nat.mul_le_mul_left _ (Nat.succ_le_succ (hload index tree)))
    _ = (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 := by
        have htree : Fintype.card ForsCoverage.Tree = 14 := by
          unfold ForsCoverage.Tree MessageDigest.ForsTree forsTrees; exact Fintype.card_fin _
        rw [Finset.prod_const, Finset.card_univ, htree, mul_pow]

/-- A load raised by one is at most twice the larger of one and itself. -/
theorem succ_pow_le (load : Nat) : (load + 1) ^ 14 ≤ 2 ^ 14 * (1 + load ^ 14) := by
  rcases Nat.eq_zero_or_pos load with rfl | hpos
  · norm_num
  · calc (load + 1) ^ 14 ≤ (2 * load) ^ 14 := Nat.pow_le_pow_left (by omega) 14
      _ = 2 ^ 14 * load ^ 14 := by rw [mul_pow]
      _ ≤ 2 ^ 14 * (1 + load ^ 14) := Nat.mul_le_mul_left _ (by omega)

set_option exponentiation.threshold 1024 in
/-- **Two uniform views at one instance cover each other rarely.** With the loads' fourteenth
moment at most `2 ^ 102`, a uniform target is covered by the disclosures together with an
independent uniform helper at its own instance with probability at most `2 ^ -177`. -/
theorem prob_helpedBy_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) :
    Pr[fun pair : View × View => HelpedBy revealed pair.1 pair.2 |
        ($ᵗ (View × View) : ProbComp (View × View))] ≤ 1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
  classical
  have hsum : ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 ≤ 2 ^ 285 := by
    have hone : ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 ≤
        ∑ index : Instance, (2 ^ 12) ^ 14 * (2 ^ 14 * (1 + loads index ^ 14)) :=
      Finset.sum_le_sum fun index _ => Nat.mul_le_mul_left _ (succ_pow_le _)
    refine le_trans hone ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ]
    have hcard : Fintype.card Instance = 2 ^ 63 := by
      unfold ForsCoverage.Instance MessageDigest.Instance totalHeight
      exact Fintype.card_fin _
    rw [hcard, smul_eq_mul, mul_one]
    calc (2 ^ 12) ^ 14 * (2 ^ 14 * (2 ^ 63 + ∑ index : Instance, loads index ^ 14))
        ≤ (2 ^ 12) ^ 14 * (2 ^ 14 * (2 ^ 63 + 2 ^ 102)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left hmoment _))
      _ ≤ 2 ^ 285 := by norm_num
  rw [probEvent_uniformSample]
  have hcard : Fintype.card (View × View) = 2 ^ 462 := by
    simp only [View, Instance, ForsCoverage.Tree, Leaf, MessageDigest.View,
      MessageDigest.Instance, MessageDigest.ForsTree, MessageDigest.ForsLeaf, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, totalHeight, forsHeight, forsTrees]
    norm_num
  rw [hcard]
  calc ((Finset.univ.filter fun pair : View × View => HelpedBy revealed pair.1 pair.2).card :
        ℝ≥0∞) / ((2 ^ 462 : Nat) : ℝ≥0∞)
      ≤ ((2 ^ 285 : Nat) : ℝ≥0∞) / ((2 ^ 462 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right
          (Nat.cast_le.mpr ((card_helped_le revealed loads hload).trans hsum)) _
    _ = 1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num

set_option exponentiation.threshold 1024 in
/-- **A uniform view lands on a given instance with probability `2 ^ -63`.** -/
theorem prob_instance_eq (index : Instance) :
    Pr[fun view : View => view.1 = index | ($ᵗ View : ProbComp View)] ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample]
  have hcount : (Finset.univ.filter fun view : View => view.1 = index).card = 2 ^ 168 := by
    have hset : (Finset.univ.filter fun view : View => view.1 = index) =
        Finset.univ.image fun leaves : Tree → Leaf => (index, leaves) := by
      ext view
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hview
        exact ⟨view.2, Prod.ext hview.symm rfl⟩
      · rintro ⟨leaves, rfl⟩
        rfl
    rw [hset, Finset.card_image_of_injective _ (fun left right h => (Prod.mk.inj h).2),
      Finset.card_univ]
    simp only [ForsCoverage.Tree, Leaf, MessageDigest.ForsTree, MessageDigest.ForsLeaf,
      Fintype.card_fun, Fintype.card_fin, forsHeight, forsTrees]
    norm_num
  have hcard : Fintype.card View = 2 ^ 231 := by
    simp only [View, Instance, ForsCoverage.Tree, Leaf, MessageDigest.View,
      MessageDigest.Instance, MessageDigest.ForsTree, MessageDigest.ForsLeaf, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, totalHeight, forsHeight, forsTrees]
    norm_num
  rw [hcount, hcard]
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-! ## Expectations against a padded block, with one cell redrawn -/

/-- **An expectation against a bind is the outer expectation of the inner ones.** -/
theorem tsum_probOutput_bind {α β : Type} (outer : ProbComp α) (inner : α → ProbComp β)
    (f : β → ℝ≥0∞) :
    ∑' out, Pr[= out | outer >>= inner] * f out =
      ∑' value, Pr[= value | outer] * ∑' out, Pr[= out | inner value] * f out := by
  calc ∑' out, Pr[= out | outer >>= inner] * f out
      = ∑' out, ∑' value, Pr[= value | outer] * Pr[= out | inner value] * f out :=
        tsum_congr fun out => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right]
    _ = ∑' value, ∑' out, Pr[= value | outer] * Pr[= out | inner value] * f out :=
        ENNReal.tsum_comm
    _ = _ := tsum_congr fun value => by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun out => by rw [mul_assoc]

/-- **An expectation against a point mass is the value at the point.** -/
theorem tsum_probOutput_pure {β : Type} (point : β) (f : β → ℝ≥0∞) :
    ∑' out, Pr[= out | (pure point : ProbComp β)] * f out = f point := by
  rw [tsum_eq_single point (fun other hother => by
    rw [probOutput_eq_zero_of_not_mem_support (by simpa using hother), zero_mul]),
    probOutput_pure_self, one_mul]

/-- **Redrawing one cell of a padded block keeps any expectation.** The expectation form of
`TapeFactor.evalDist_padding_set`. -/
theorem tsum_padding_set (length cell : Nat) (hcell : cell < length)
    (f : List HashOutput → ℝ≥0∞) :
    ∑' tape, Pr[= tape | padding length] * f tape =
      ∑' tape, Pr[= tape | padding length] *
        ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] * f (tape.set cell value) := by
  classical
  have hlaw := TapeFactor.evalDist_padding_set length cell hcell
    (fun tape => (pure tape : ProbComp (List HashOutput)))
  simp only [bind_pure] at hlaw
  calc ∑' tape, Pr[= tape | padding length] * f tape
      = ∑' out, Pr[= out | padding length >>= fun tape =>
          ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            (pure (tape.set cell value) : ProbComp (List HashOutput))] * f out :=
        tsum_congr fun out => by rw [probOutput_def, probOutput_def, hlaw]
    _ = _ := by
        rw [tsum_probOutput_bind]
        refine tsum_congr fun tape => congrArg _ ?_
        rw [tsum_probOutput_bind]
        exact tsum_congr fun value => by rw [tsum_probOutput_pure]

section Tape

variable {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ) (len : ρ → Nat)

/-- **The expected weight on the runs that reach target cell `index`**, with both blocks drawn
first. A weight that reads the blocks only is a fact about the blocks; this keeps it beside the
selection, which is what lets one cell be redrawn under it. -/
noncomputable def reachMass (leftLength rightLength index : Nat)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' leftTape, Pr[= leftTape | padding leftLength] *
    ∑' rightTape, Pr[= rightTape | padding rightLength] *
      (weight leftTape rightTape * Pr[fun z => index < len z | run leftTape rightTape])

open scoped Classical in
/-- **A block event beside the selection is a reach mass.** -/
theorem probEvent_reach_and_eq (leftLength rightLength index : Nat)
    (event : List HashOutput → List HashOutput → Prop) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < len outcome.2 ∧ event outcome.1.1 outcome.1.2 |
      blockRunOf run leftLength rightLength] =
      reachMass run len leftLength rightLength index
        (fun leftTape rightTape => if event leftTape rightTape then 1 else 0) := by
  classical
  rw [blockRunOf, probEvent_bind_eq_tsum, reachMass]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [probEvent_map]
  have hswap : Pr[(fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < len outcome.2 ∧ event outcome.1.1 outcome.1.2) ∘
          (fun result => ((leftTape, rightTape), result)) | run leftTape rightTape] =
      Pr[fun z => event leftTape rightTape ∧ index < len z | run leftTape rightTape] :=
    probEvent_congr' (fun z _ => and_comm) rfl
  rw [hswap, TapeFactor.probEvent_const_and]
  split <;> simp

/-- The selection alone is the reach mass of the unit weight. -/
theorem probEvent_reach_eq (leftLength rightLength index : Nat) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ => index < len outcome.2 |
      blockRunOf run leftLength rightLength] =
      reachMass run len leftLength rightLength index (fun _ _ => 1) := by
  classical
  have h := probEvent_reach_and_eq run len leftLength rightLength index (fun _ _ => True)
  simp only [and_true, if_true] at h
  exact h

/-- **The blocked run's events, as a double expectation over the two blocks.** -/
theorem probEvent_blockRunOf_eq (leftLength rightLength : Nat)
    (event : (List HashOutput × List HashOutput) × ρ → Prop) :
    Pr[event | blockRunOf run leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] *
          Pr[fun z => event ((leftTape, rightTape), z) | run leftTape rightTape] := by
  rw [blockRunOf, probEvent_bind_eq_tsum]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [probEvent_bind_eq_tsum]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [probEvent_map]
  rfl

/-- **A constant comes out of a reach mass.** -/
theorem reachMass_const_mul (leftLength rightLength index : Nat) (constant : ℝ≥0∞)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength index
        (fun leftTape rightTape => constant * weight leftTape rightTape) =
      constant * reachMass run len leftLength rightLength index weight := by
  simp only [reachMass, mul_assoc, mul_left_comm _ constant, ENNReal.tsum_mul_left]

/-- **Redrawing a cell the selection does not read keeps the reach mass**, with the weight
averaged over the redrawn cell. -/
theorem reachMass_resample (leftLength rightLength index cell : Nat) (hcell : cell < rightLength)
    (hcausal : ∀ (leftTape rightTape : List HashOutput) (value : HashOutput),
      Pr[fun z => index < len z | run leftTape (rightTape.set cell value)] =
        Pr[fun z => index < len z | run leftTape rightTape])
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength index weight =
      reachMass run len leftLength rightLength index (fun leftTape rightTape =>
        ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
          weight leftTape (rightTape.set cell value)) := by
  rw [reachMass, reachMass]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [tsum_padding_set rightLength cell hcell]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun value => ?_
  rw [hcausal leftTape rightTape value, mul_assoc]

/-- **A later cell is reached only on runs that reach an earlier one.** -/
theorem reachMass_mono_index (leftLength rightLength : Nat) {early late : Nat}
    (horder : early ≤ late) (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength late weight ≤
      reachMass run len leftLength rightLength early weight := by
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => mul_le_mul' le_rfl ?_
  exact mul_le_mul' le_rfl (probEvent_mono fun z _ hlate => lt_of_le_of_lt horder hlate)

/-- **Weights add under a reach mass**, and it is monotone in them. -/
theorem reachMass_mono_weight (leftLength rightLength index : Nat)
    {small large : List HashOutput → List HashOutput → ℝ≥0∞}
    (hle : ∀ leftTape rightTape, small leftTape rightTape ≤ large leftTape rightTape) :
    reachMass run len leftLength rightLength index small ≤
      reachMass run len leftLength rightLength index large := by
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => mul_le_mul' le_rfl ?_
  exact mul_le_mul' (hle leftTape rightTape) le_rfl

/-- **A bounded weight costs its bound times the probability of reaching the cell.** -/
theorem reachMass_le_const (leftLength rightLength index : Nat)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) (bound : ℝ≥0∞)
    (hbound : ∀ leftTape rightTape, weight leftTape rightTape ≤ bound) :
    reachMass run len leftLength rightLength index weight ≤
      bound * Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < len outcome.2 | blockRunOf run leftLength rightLength] := by
  rw [probEvent_reach_eq run len leftLength rightLength index,
    ← reachMass_const_mul run len leftLength rightLength index bound, ]
  exact reachMass_mono_weight run len leftLength rightLength index
    fun leftTape rightTape => by rw [mul_one]; exact hbound leftTape rightTape

/-- **A thinning, integrated over the blocks.** An event of the run whose probability, for every
pair of blocks, is at most `rate` times that of reaching cell `index` costs `rate` times the reach
mass of any block event beside it. -/
theorem prob_thin_le (leftLength rightLength index : Nat) (thinned : ρ → Prop)
    (rate : ℝ≥0∞)
    (hthin : ∀ leftTape rightTape, Pr[thinned | run leftTape rightTape] ≤
      rate * Pr[fun z => index < len z | run leftTape rightTape])
    (event : List HashOutput → List HashOutput → Prop)
    [∀ leftTape rightTape, Decidable (event leftTape rightTape)] :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        thinned outcome.2 ∧ event outcome.1.1 outcome.1.2 |
      blockRunOf run leftLength rightLength] ≤
      rate * reachMass run len leftLength rightLength index
        (fun leftTape rightTape => if event leftTape rightTape then 1 else 0) := by
  classical
  rw [← reachMass_const_mul, probEvent_blockRunOf_eq, reachMass]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => mul_le_mul' le_rfl ?_
  by_cases hevent : event leftTape rightTape
  · rw [if_pos hevent, mul_one]
    refine le_trans (le_of_eq (probEvent_congr' (fun z _ => ?_) rfl)) (hthin leftTape rightTape)
    simp [hevent]
  · rw [if_neg hevent, mul_zero, zero_mul]
    exact le_of_eq (probEvent_eq_zero fun z _ hz => hevent hz.2)

/-- **A weight bounded on the padded blocks costs its bound times the reach probability.** The
padded blocks have their lengths, so a bound need only hold there. -/
theorem reachMass_le_const_of_length (leftLength rightLength index : Nat)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) (bound : ℝ≥0∞)
    (hbound : ∀ leftTape rightTape, rightTape.length = rightLength →
      weight leftTape rightTape ≤ bound) :
    reachMass run len leftLength rightLength index weight ≤
      bound * Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < len outcome.2 | blockRunOf run leftLength rightLength] := by
  classical
  rw [probEvent_reach_eq run len leftLength rightLength index,
    ← reachMass_const_mul run len leftLength rightLength index bound]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => ?_
  by_cases hmem : rightTape ∈ support (padding rightLength)
  · refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
    rw [mul_one]
    exact hbound leftTape rightTape (padding_length rightLength rightTape hmem)
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

end Tape

/-! ## The wide event, and how it falls into four -/

/-- The parsed view at one cell of a block. -/
def cellView (tape : List HashOutput) (index : Nat) : View :=
  MessageDigest.parse (tape.getD index default)

/-- A witness view supplies the target's leaf at one tree, at the target's own instance. -/
def Supplies (witness target : View) (tree : Tree) : Prop :=
  witness.1 = target.1 ∧ witness.2 tree = target.2 tree

/-- The disclosing block's loads are below the sharper cap. -/
def GoodLeft (leftLength : Nat) (leftTape : List HashOutput) : Prop :=
  ∑ part, ForsDisclosureTape.loads (blockTape leftLength leftTape) part ^ 14 ≤ 2 ^ 102

/-- The disclosures of the whole disclosing block. -/
def leftDisclosures (leftLength : Nat) (leftTape : List HashOutput) : Disclosures :=
  ForsDisclosureTape.disclosures (blockTape leftLength leftTape)

/-- **The wide coverage event, in the blocks' coordinates.** Some reached target cell has each of
its fourteen leaves supplied, at its own instance, by a cell of the disclosing block or by
another reached target cell that fired. -/
def FiredCovered {ρ : Type} (len : ρ → Nat) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (outcome : (List HashOutput × List HashOutput) × ρ) : Prop :=
  ∃ target < rightLength, target < len outcome.2 ∧ ∀ tree,
    (∃ cell < leftLength,
      Supplies (cellView outcome.1.1 cell) (cellView outcome.1.2 target) tree) ∨
    (∃ helper < rightLength, helper < len outcome.2 ∧ helper ≠ target ∧
      fired outcome.2 helper ∧
      Supplies (cellView outcome.1.2 helper) (cellView outcome.1.2 target) tree)

/-- A leaf supplied by a block cell is a disclosed leaf of the block. -/
theorem mem_leftDisclosures {leftLength : Nat} {leftTape : List HashOutput} {view : View}
    {tree : Tree}
    (hcell : ∃ cell < leftLength, Supplies (cellView leftTape cell) view tree) :
    view.2 tree ∈ leftDisclosures leftLength leftTape view.1 tree := by
  obtain ⟨cell, hlt, hinstance, hleaf⟩ := hcell
  refine Finset.mem_image.mpr ⟨⟨cell, hlt⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hinstance
  · exact hleaf

open scoped Classical in
/-- **The wide event falls into four.** The block is bad; or the target is covered by the block
alone; or exactly one fired cell at its instance helps; or two fired cells share an instance. -/
theorem firedCovered_cases {ρ : Type} (len : ρ → Nat) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (leftTape rightTape : List HashOutput) (z : ρ)
    (hcovered : FiredCovered len fired leftLength rightLength ((leftTape, rightTape), z)) :
    ¬ GoodLeft leftLength leftTape ∨
      (∃ target < rightLength, target < len z ∧ GoodLeft leftLength leftTape ∧
        Covered (leftDisclosures leftLength leftTape) (cellView rightTape target)) ∨
      (∃ target < rightLength, ∃ helper < rightLength, target ≠ helper ∧
        (helper < len z ∧ fired z helper) ∧
        (GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
          (cellView rightTape target) (cellView rightTape helper))) ∨
      (∃ first < rightLength, ∃ second < rightLength, first < second ∧
        (second < len z ∧ fired z first ∧ fired z second) ∧
        (cellView rightTape first).1 = (cellView rightTape second).1) := by
  classical
  obtain ⟨target, htarget, hreached, htrees⟩ := hcovered
  by_cases hgood : GoodLeft leftLength leftTape
  swap
  · exact Or.inl hgood
  refine Or.inr ?_
  -- Two distinct fired cells at the target's instance.
  by_cases htwo : ∃ first < rightLength, ∃ second < rightLength, first ≠ second ∧
      first < len z ∧ second < len z ∧ fired z first ∧ fired z second ∧
      (cellView rightTape first).1 = (cellView rightTape target).1 ∧
      (cellView rightTape second).1 = (cellView rightTape target).1
  · obtain ⟨first, hfirst, second, hsecond, hne, hfirstLen, hsecondLen, hfirstFired,
      hsecondFired, hfirstInst, hsecondInst⟩ := htwo
    refine Or.inr (Or.inr ?_)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, hfirst, second, hsecond, hlt, ⟨hsecondLen, hfirstFired, hsecondFired⟩,
        hfirstInst.trans hsecondInst.symm⟩
    · exact ⟨second, hsecond, first, hfirst, hgt, ⟨hfirstLen, hsecondFired, hfirstFired⟩,
        hsecondInst.trans hfirstInst.symm⟩
  -- At most one; if there is one, it helps.
  by_cases hone : ∃ helper < rightLength, helper < len z ∧ helper ≠ target ∧ fired z helper ∧
      (cellView rightTape helper).1 = (cellView rightTape target).1
  · obtain ⟨helper, hhelper, hhelperLen, hne, hfired, hinstance⟩ := hone
    refine Or.inr (Or.inl ⟨target, htarget, helper, hhelper, hne.symm, ⟨hhelperLen, hfired⟩,
      hgood, hinstance, fun tree => ?_⟩)
    rcases htrees tree with hblock | ⟨other, hother, hotherLen, hotherNe, hotherFired,
      hotherInstance, hotherLeaf⟩
    · exact Or.inl (mem_leftDisclosures hblock)
    · by_cases hsame : other = helper
      · subst hsame
        exact Or.inr hotherLeaf
      · exact absurd ⟨other, hother, helper, hhelper, hsame, hotherLen, hhelperLen,
          hotherFired, hfired, hotherInstance, hinstance⟩ htwo
  · refine Or.inl ⟨target, htarget, hreached, hgood, fun tree => ?_⟩
    rcases htrees tree with hblock | ⟨other, hother, hotherLen, hotherNe, hotherFired,
      hotherInstance, -⟩
    · exact mem_leftDisclosures hblock
    · exact absurd ⟨other, hother, hotherLen, hotherNe, hotherFired, hotherInstance⟩ hone

/-! ## The two rates, at fresh answers -/

/-- An indicator's expectation is its event's probability. -/
theorem tsum_ite_eq_probEvent {α : Type} (computation : ProbComp α) (event : α → Prop)
    [DecidablePred event] :
    ∑' value, Pr[= value | computation] * (if event value then 1 else 0) =
      Pr[event | computation] := by
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun value => ?_
  split <;> simp

/-- **Two fresh answers parse to two independent uniform views.** -/
theorem evalDist_parse_pair :
    𝒟[(fun pair : HashOutput × HashOutput =>
        (MessageDigest.parse pair.1, MessageDigest.parse pair.2)) <$>
      ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))] =
      𝒟[($ᵗ (View × View) : ProbComp (View × View))] := by
  rw [uniformSample_prod_eq_bind, uniformSample_prod_eq_bind]
  have hshape : ((fun pair : HashOutput × HashOutput =>
        (MessageDigest.parse pair.1, MessageDigest.parse pair.2)) <$>
      (do let left ← ($ᵗ HashOutput : ProbComp HashOutput)
          let right ← ($ᵗ HashOutput : ProbComp HashOutput)
          pure (left, right))) =
      (do let left ← MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)
          let right ← MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)
          pure (left, right)) := by
    simp only [map_bind, map_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def]
  rw [hshape, evalDist_bind, evalDist_parse_uniform, evalDist_bind]
  refine congrArg _ (funext fun left => ?_)
  rw [evalDist_bind, evalDist_parse_uniform, evalDist_bind]

open scoped Classical in
/-- **The pair rate at fresh answers**: two fresh answers parse to a helped pair with probability
at most `2 ^ -177`, as a double expectation. -/
theorem tsum_pair_helpedBy_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) :
    ∑' first, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' second, Pr[= second | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if HelpedBy revealed (MessageDigest.parse first) (MessageDigest.parse second)
          then 1 else 0) ≤ 1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
  classical
  have hdouble : (∑' first, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' second, Pr[= second | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if HelpedBy revealed (MessageDigest.parse first) (MessageDigest.parse second)
          then 1 else 0)) =
      Pr[fun pair : HashOutput × HashOutput =>
          HelpedBy revealed (MessageDigest.parse pair.1) (MessageDigest.parse pair.2) |
        ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))] := by
    rw [uniformSample_prod_eq_bind, probEvent_bind_eq_tsum]
    refine tsum_congr fun first => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun second => congrArg _ ?_
    rw [probEvent_pure]
  rw [hdouble]
  have hmap : Pr[fun pair : HashOutput × HashOutput =>
          HelpedBy revealed (MessageDigest.parse pair.1) (MessageDigest.parse pair.2) |
        ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))] =
      Pr[fun pair : View × View => HelpedBy revealed pair.1 pair.2 |
        ($ᵗ (View × View) : ProbComp (View × View))] := by
    rw [← probEvent_congr' (fun _ _ => Iff.rfl) evalDist_parse_pair, probEvent_map]
    rfl
  rw [hmap]
  exact prob_helpedBy_le revealed loads hload hmoment

open scoped Classical in
/-- **The instance rate at a fresh answer**, as an expectation. -/
theorem tsum_instance_eq_le (index : Instance) :
    ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if (MessageDigest.parse value).1 = index then 1 else 0) ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) := by
  classical
  rw [tsum_ite_eq_probEvent]
  have hmap : Pr[fun value => (MessageDigest.parse value).1 = index |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[fun view : View => view.1 = index | ($ᵗ View : ProbComp View)] := by
    rw [← probEvent_congr' (fun _ _ => Iff.rfl) evalDist_parse_uniform, probEvent_map]
    rfl
  rw [hmap]
  exact prob_instance_eq index

/-- Reading back the cell just overwritten. -/
theorem cellView_set_self {tape : List HashOutput} {index : Nat} (hindex : index < tape.length)
    (value : HashOutput) : cellView (tape.set index value) index = MessageDigest.parse value := by
  simp [cellView, List.getD_eq_getElem?_getD, hindex]

/-- Reading a cell other than the one overwritten. -/
theorem cellView_set_ne {tape : List HashOutput} {index other : Nat} (hne : index ≠ other)
    (value : HashOutput) : cellView (tape.set index value) other = cellView tape other := by
  simp [cellView, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

/-! ## The charges, cell by cell -/

/-- Two expectations commute. -/
theorem tsum_tsum_swap (f : HashOutput → HashOutput → ℝ≥0∞) :
    ∑' first, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' second, Pr[= second | ($ᵗ HashOutput : ProbComp HashOutput)] * f first second =
    ∑' second, Pr[= second | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' first, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] * f first second := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun second => tsum_congr fun first => by ring

section Charges

variable {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ) (len : ρ → Nat)

open scoped Classical in
/-- **One fired helper, at the reach mass of the helper's cell.** Redraw the later of the two
cells and then the earlier: what is left is the pair rate, paid once per reached cell. -/
theorem reachMass_helped_le (leftLength rightLength target helper : Nat)
    (htarget : target < rightLength) (hhelper : helper < rightLength) (hne : target ≠ helper)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr[fun z => index < len z | run leftTape (rightTape.set cell value)] =
          Pr[fun z => index < len z | run leftTape rightTape]) :
    reachMass run len leftLength rightLength helper (fun leftTape rightTape =>
        if GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
            (cellView rightTape target) (cellView rightTape helper) then 1 else 0) ≤
      1 / ((2 ^ 177 : Nat) : ℝ≥0∞) *
        (Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
            target < len outcome.2 | blockRunOf run leftLength rightLength] +
          Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
            helper < len outcome.2 | blockRunOf run leftLength rightLength]) := by
  classical
  -- The pair rate, once both cells are fresh.
  have hpair : ∀ leftTape : List HashOutput,
      ∑' w, Pr[= w | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
            (MessageDigest.parse w) (MessageDigest.parse v) then 1 else 0) ≤
        1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
    intro leftTape
    by_cases hgood : GoodLeft leftLength leftTape
    · simp only [hgood, true_and]
      exact tsum_pair_helpedBy_le (leftDisclosures leftLength leftTape)
        (ForsDisclosureTape.loads (blockTape leftLength leftTape))
        (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree) hgood
    · simp [hgood]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- the target is the earlier cell
    rw [reachMass_resample run len leftLength rightLength helper helper hhelper
      (fun leftTape rightTape value => hcausal helper helper leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_mono_index run len leftLength rightLength (le_of_lt hlt) _) ?_
    rw [reachMass_resample run len leftLength rightLength target target htarget
      (fun leftTape rightTape value => hcausal target target leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_le_const_of_length run len leftLength rightLength target _ _
      fun leftTape rightTape hlength => ?_) (mul_le_mul' le_rfl le_self_add)
    refine le_of_eq_of_le (tsum_congr fun w => congrArg _ (tsum_congr fun v => ?_))
      (hpair leftTape)
    rw [cellView_set_ne (Ne.symm hne), cellView_set_self (by rw [hlength]; exact htarget),
      cellView_set_self (by rw [List.length_set, hlength]; exact hhelper)]
  · -- the helper is the earlier cell
    rw [reachMass_resample run len leftLength rightLength helper target htarget
      (fun leftTape rightTape value => hcausal helper target leftTape rightTape value
        (le_of_lt hgt))]
    rw [reachMass_resample run len leftLength rightLength helper helper hhelper
      (fun leftTape rightTape value => hcausal helper helper leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_le_const_of_length run len leftLength rightLength helper _ _
      fun leftTape rightTape hlength => ?_) (mul_le_mul' le_rfl le_add_self)
    refine le_of_eq_of_le ?_ (hpair leftTape)
    rw [tsum_tsum_swap]
    refine tsum_congr fun w => congrArg _ (tsum_congr fun v => ?_)
    rw [cellView_set_self (by rw [List.length_set, hlength]; exact htarget),
      cellView_set_ne hne, cellView_set_self (by rw [hlength]; exact hhelper)]

open scoped Classical in
/-- **Two cells at one instance, at the reach mass of the earlier one.** Redraw the later. -/
theorem reachMass_sameInstance_le (leftLength rightLength first second : Nat)
    (hsecond : second < rightLength) (horder : first < second)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr[fun z => index < len z | run leftTape (rightTape.set cell value)] =
          Pr[fun z => index < len z | run leftTape rightTape]) :
    reachMass run len leftLength rightLength first (fun _ rightTape =>
        if (cellView rightTape first).1 = (cellView rightTape second).1 then 1 else 0) ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) *
        Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
          first < len outcome.2 | blockRunOf run leftLength rightLength] := by
  classical
  rw [reachMass_resample run len leftLength rightLength first second hsecond
    (fun leftTape rightTape value => hcausal first second leftTape rightTape value
      (le_of_lt horder))]
  refine reachMass_le_const_of_length run len leftLength rightLength first _ _
    fun leftTape rightTape hlength => ?_
  refine le_of_eq_of_le (tsum_congr fun v => congrArg _ ?_)
    (tsum_instance_eq_le (cellView rightTape first).1)
  rw [cellView_set_ne (Nat.ne_of_gt horder), cellView_set_self (by rw [hlength]; exact hsecond)]
  exact if_congr eq_comm rfl rfl

end Charges

/-! ## The whole charge -/

/-- A blocked outcome carries two padded blocks. -/
theorem mem_support_blockRunOf {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) {outcome : (List HashOutput × List HashOutput) × ρ}
    (hmem : outcome ∈ support (blockRunOf run leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧ outcome.1.2 ∈ support (padding rightLength) := by
  rw [blockRunOf, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleft, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hright, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨z, -, rfl⟩ := hinner
  exact ⟨hleft, hright⟩

open scoped Classical in
/-- **A bad disclosing block is a fact about the block alone**, at the sharper cap. -/
theorem prob_not_goodLeft_le {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        ¬ GoodLeft leftLength outcome.1.1 | blockRunOf run leftLength rightLength] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 := by
  classical
  have hblock : Pr[fun block => ¬ GoodLeft leftLength block | padding leftLength] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 := by
    have hevent : Pr[fun block => ¬ GoodLeft leftLength block | padding leftLength] =
        Pr[fun tape => 2 ^ 102 < ∑ part, ForsDisclosureTape.loads tape part ^ 14 |
          ($ᵗ (ForsDisclosureTape.Tape leftLength) :
            ProbComp (ForsDisclosureTape.Tape leftLength))] := by
      rw [← probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_blockTape leftLength),
        probEvent_map]
      exact probEvent_congr' (fun block _ => by
        simp only [Function.comp_def, GoodLeft, not_le]) rfl
    rw [hevent]
    exact ForsDisclosureTape.bad_load_probability_sharper leftLength hcap
  refine le_trans ?_ hblock
  rw [probEvent_blockRunOf_eq, ← tsum_ite_eq_probEvent]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  by_cases hgood : GoodLeft leftLength leftTape
  · simp [hgood]
  · simp only [hgood, not_false_eq_true, if_true]
    calc ∑' rightTape, Pr[= rightTape | padding rightLength] *
          Pr[fun _ : ρ => True | run leftTape rightTape]
        ≤ ∑' rightTape, Pr[= rightTape | padding rightLength] :=
          ENNReal.tsum_le_tsum fun _ => mul_le_of_le_one_right' probEvent_le_one
      _ ≤ 1 := tsum_probOutput_le_one

set_option exponentiation.threshold 1024 in
/-- The constants of the second-order terms fit under `2 ^ -303`. -/
theorem second_order_constants :
    2 * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 177 : Nat) : ℝ≥0∞))) +
        1 / ((2 ^ 256 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 63 : Nat) : ℝ≥0∞)) ≤
      1 / ((2 ^ 303 : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  norm_num

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The coverage charge with fired cells admitted as witnesses.**

The first-order term is the block's: `2 ^ -129` per expected target, at the sharper cap. The
fired cells cost `rightLength · 2 ^ -303` per expected target, which at any `rightLength ≤ 2 ^ 128`
is far inside the other half unit. -/
theorem prob_firedCovered_le {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr[fun z => index < (rightOfResult z).length | run leftTape (rightTape.set cell value)] =
          Pr[fun z => index < (rightOfResult z).length | run leftTape rightTape])
    (hthin1 : ∀ (index : Nat) (leftTape rightTape : List HashOutput),
      Pr[fun z => index < (rightOfResult z).length ∧ fired z index | run leftTape rightTape] ≤
        1 / ((2 ^ 128 : Nat) : ℝ≥0∞) *
          Pr[fun z => index < (rightOfResult z).length | run leftTape rightTape])
    (hthin2 : ∀ (first second : Nat) (leftTape rightTape : List HashOutput), first < second →
      Pr[fun z => second < (rightOfResult z).length ∧ fired z first ∧ fired z second |
          run leftTape rightTape] ≤
        1 / ((2 ^ 256 : Nat) : ℝ≥0∞) *
          Pr[fun z => first < (rightOfResult z).length | run leftTape rightTape]) :
    Pr[FiredCovered (fun z => (rightOfResult z).length) fired leftLength rightLength |
        blockRunOf run leftLength rightLength] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 +
        (∑' outcome, Pr[= outcome | blockRunOf run leftLength rightLength] *
            (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) *
          (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) +
        (rightLength : ℝ≥0∞) *
          (∑' outcome, Pr[= outcome | blockRunOf run leftLength rightLength] *
            (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) *
          (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
  classical
  set len : ρ → Nat := fun z => (rightOfResult z).length with hlen
  set expectation := ∑' outcome, Pr[= outcome | blockRunOf run leftLength rightLength] *
    (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) with hexpectation
  set reach : Nat → ℝ≥0∞ := fun index =>
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ => index < len outcome.2 |
      blockRunOf run leftLength rightLength] with hreach
  have hsum : ∑ index : Fin rightLength, reach index.val ≤ expectation :=
    sum_prob_selected_le_expected_of run rightOfResult leftLength rightLength
  -- The four events.
  set eventA : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ index : Fin rightLength, index.val < (rightOfResult outcome.2).length ∧
      GoodLeft leftLength outcome.1.1 ∧
        ∃ value, outcome.1.2[index.val]? = some value ∧ BlockHit leftLength outcome.1.1 value
    with heventA
  set eventB : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ pair ∈ (Finset.univ : Finset (Fin rightLength × Fin rightLength)),
      pair.1.val ≠ pair.2.val ∧
        ((pair.2.val < len outcome.2 ∧ fired outcome.2 pair.2.val) ∧
          (GoodLeft leftLength outcome.1.1 ∧ HelpedBy (leftDisclosures leftLength outcome.1.1)
            (cellView outcome.1.2 pair.1.val) (cellView outcome.1.2 pair.2.val))) with heventB
  set eventC : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ pair ∈ (Finset.univ : Finset (Fin rightLength × Fin rightLength)),
      pair.1.val < pair.2.val ∧
        ((pair.2.val < len outcome.2 ∧ fired outcome.2 pair.1.val ∧ fired outcome.2 pair.2.val) ∧
          (cellView outcome.1.2 pair.1.val).1 = (cellView outcome.1.2 pair.2.val).1)
    with heventC
  have hsplit : Pr[FiredCovered len fired leftLength rightLength |
        blockRunOf run leftLength rightLength] ≤
      Pr[fun outcome => ¬ GoodLeft leftLength outcome.1.1 |
          blockRunOf run leftLength rightLength] +
        (Pr[eventA | blockRunOf run leftLength rightLength] +
          (Pr[eventB | blockRunOf run leftLength rightLength] +
            Pr[eventC | blockRunOf run leftLength rightLength])) := by
    refine le_trans (probEvent_mono (q := fun outcome =>
      ¬ GoodLeft leftLength outcome.1.1 ∨ (eventA outcome ∨ (eventB outcome ∨ eventC outcome)))
      fun outcome hmem hcovered => ?_) ?_
    · have hlength := padding_length rightLength outcome.1.2
        (mem_support_blockRunOf run leftLength rightLength hmem).2
      rcases firedCovered_cases len fired leftLength rightLength outcome.1.1 outcome.1.2
          outcome.2 hcovered with hbad | ⟨target, htarget, hreached, hgood, hcov⟩ |
          ⟨target, htarget, helper, hhelper, hne, hthin, hhelp⟩ |
          ⟨first, hfirst, second, hsecond, horder, hthin, hinstance⟩
      · exact Or.inl hbad
      · refine Or.inr (Or.inl ⟨⟨target, htarget⟩, hreached, hgood,
          outcome.1.2.getD target default, ?_, hcov⟩)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlength]; exact htarget)]
        rfl
      · exact Or.inr (Or.inr (Or.inl ⟨(⟨target, htarget⟩, ⟨helper, hhelper⟩),
          Finset.mem_univ _, hne, hthin, hhelp⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(⟨first, hfirst⟩, ⟨second, hsecond⟩),
          Finset.mem_univ _, horder, hthin, hinstance⟩))
    · refine le_trans (probEvent_or_le _ _ _) (add_le_add le_rfl ?_)
      refine le_trans (probEvent_or_le _ _ _) (add_le_add le_rfl ?_)
      exact probEvent_or_le _ _ _
  -- The block alone.
  have hbad := prob_not_goodLeft_le run leftLength rightLength hcap
  -- The first-order term.
  have hfirstOrder : Pr[eventA | blockRunOf run leftLength rightLength] ≤
      expectation * (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) :=
    NoticingTape.prob_exists_hit_le_expected_of_causal run rightOfResult leftLength rightLength
      (GoodLeft leftLength) (BlockHit leftLength) (1 / ((2 ^ 129 : Nat) : ℝ≥0∞))
      (fun leftTape hgood => by
        refine le_trans (le_of_eq ?_) (ForsCoverage.fresh_coverage_le_sharper
          (ForsDisclosureTape.disclosures (blockTape leftLength leftTape))
          (ForsDisclosureTape.loads (blockTape leftLength leftTape))
          (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree) hgood)
        rw [← probEvent_congr' (fun _ _ => Iff.rfl) evalDist_parse_uniform, probEvent_map]
        rfl)
      (fun index leftTape rightTape value => hcausal index index leftTape rightTape value le_rfl)
  -- One fired helper.
  set pairRate : ℝ≥0∞ := 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 177 : Nat) : ℝ≥0∞))
    with hpairRate
  have hhelped : Pr[eventB | blockRunOf run leftLength rightLength] ≤
      ∑ pair : Fin rightLength × Fin rightLength,
        pairRate * (reach pair.1.val + reach pair.2.val) := by
    refine le_trans (probEvent_exists_finset_le_sum _ _ _) (Finset.sum_le_sum fun pair _ => ?_)
    by_cases hsame : pair.1.val = pair.2.val
    · rw [probEvent_eq_zero fun outcome _ hevent => hevent.1 hsame]
      exact bot_le
    · rw [probEvent_congr' (q := fun outcome : (List HashOutput × List HashOutput) × ρ =>
          (pair.2.val < len outcome.2 ∧ fired outcome.2 pair.2.val) ∧
            (GoodLeft leftLength outcome.1.1 ∧
              HelpedBy (leftDisclosures leftLength outcome.1.1)
                (cellView outcome.1.2 pair.1.val) (cellView outcome.1.2 pair.2.val)))
          (fun outcome _ => ⟨fun h => h.2, fun h => ⟨hsame, h⟩⟩) rfl]
      refine le_trans (prob_thin_le run len leftLength rightLength pair.2.val
        (fun z => pair.2.val < len z ∧ fired z pair.2.val) _
        (fun leftTape rightTape => hthin1 pair.2.val leftTape rightTape)
        (fun leftTape rightTape => GoodLeft leftLength leftTape ∧
          HelpedBy (leftDisclosures leftLength leftTape)
            (cellView rightTape pair.1.val) (cellView rightTape pair.2.val))) ?_
      rw [hpairRate, mul_assoc]
      exact mul_le_mul' le_rfl (reachMass_helped_le run len leftLength rightLength
        pair.1.val pair.2.val pair.1.isLt pair.2.isLt hsame hcausal)
  -- Two fired cells at one instance.
  set twoRate : ℝ≥0∞ := 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 63 : Nat) : ℝ≥0∞))
    with htwoRate
  have htwo : Pr[eventC | blockRunOf run leftLength rightLength] ≤
      ∑ pair : Fin rightLength × Fin rightLength, twoRate * reach pair.1.val := by
    refine le_trans (probEvent_exists_finset_le_sum _ _ _) (Finset.sum_le_sum fun pair _ => ?_)
    by_cases horder : pair.1.val < pair.2.val
    · rw [probEvent_congr' (q := fun outcome : (List HashOutput × List HashOutput) × ρ =>
          (pair.2.val < len outcome.2 ∧ fired outcome.2 pair.1.val ∧
              fired outcome.2 pair.2.val) ∧
            (cellView outcome.1.2 pair.1.val).1 = (cellView outcome.1.2 pair.2.val).1)
          (fun outcome _ => ⟨fun h => h.2, fun h => ⟨horder, h⟩⟩) rfl]
      refine le_trans (prob_thin_le run len leftLength rightLength pair.1.val
        (fun z => pair.2.val < len z ∧ fired z pair.1.val ∧ fired z pair.2.val) _
        (fun leftTape rightTape => hthin2 pair.1.val pair.2.val leftTape rightTape horder)
        (fun _ rightTape =>
          (cellView rightTape pair.1.val).1 = (cellView rightTape pair.2.val).1)) ?_
      rw [htwoRate, mul_assoc]
      exact mul_le_mul' le_rfl (reachMass_sameInstance_le run len leftLength rightLength
        pair.1.val pair.2.val pair.2.isLt horder hcausal)
    · rw [probEvent_eq_zero fun outcome _ hevent => horder hevent.1]
      exact bot_le
  -- Summing the pairs.
  have hpairs : ∑ pair : Fin rightLength × Fin rightLength,
        pairRate * (reach pair.1.val + reach pair.2.val) +
      ∑ pair : Fin rightLength × Fin rightLength, twoRate * reach pair.1.val ≤
      (rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
    have hfirst : ∑ pair : Fin rightLength × Fin rightLength, reach pair.1.val =
        (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
    have hsecond : ∑ pair : Fin rightLength × Fin rightLength, reach pair.2.val =
        (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hfirst, hsecond]
    calc pairRate * ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val +
            (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val) +
          twoRate * ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val)
        = (2 * pairRate + twoRate) *
            ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val) := by ring
      _ ≤ (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) * ((rightLength : ℝ≥0∞) * expectation) :=
          mul_le_mul' second_order_constants (mul_le_mul' le_rfl hsum)
      _ = (rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by ring
  calc Pr[FiredCovered len fired leftLength rightLength | blockRunOf run leftLength rightLength]
      ≤ _ := hsplit
    _ ≤ (1 : ℝ≥0∞) / 2 ^ 126 + (expectation * (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) +
          ((rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)))) :=
        add_le_add hbad (add_le_add hfirstOrder
          (le_trans (add_le_add hhelped htwo) hpairs))
    _ = _ := by ring

end SlhDsaSecurity.FiredCoverage

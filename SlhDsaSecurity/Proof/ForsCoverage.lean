import SlhDsaSecurity.Statement.Parameters
import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# FORS coverage for an independent target

The target here is a fresh uniform index and fourteen fresh uniform leaf indices. This
file does not identify that distribution with an adaptively selected message digest.
The counting equivalence follows `LeanSphincs/ForsCoverage.lean` in the local
`leansphincs-candidate` reference, specialized to the standard dimensions.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ForsCoverage

abbrev Instance := Fin (2 ^ totalHeight)
abbrev Tree := Fin forsTrees
abbrev Leaf := Fin (2 ^ forsHeight)
abbrev View := Instance × (Tree → Leaf)
abbrev Disclosures := Instance → Tree → Finset Leaf

def Covered (revealed : Disclosures) (view : View) : Prop :=
  ∀ tree, view.2 tree ∈ revealed view.1 tree

instance (revealed : Disclosures) : DecidablePred (Covered revealed) :=
  fun view => inferInstanceAs (Decidable (∀ tree, view.2 tree ∈ revealed view.1 tree))

def coveredEquiv (revealed : Disclosures) :
    (Σ index : Instance, (tree : Tree) → {leaf : Leaf // leaf ∈ revealed index tree}) ≃
      {view : View // Covered revealed view} where
  toFun choice := ⟨(choice.1, fun tree => (choice.2 tree).val), fun tree => (choice.2 tree).property⟩
  invFun view := ⟨view.val.1, fun tree => ⟨view.val.2 tree, view.property tree⟩⟩
  left_inv := by rintro ⟨index, leaves⟩; rfl
  right_inv := by rintro ⟨⟨index, leaves⟩, h⟩; rfl

theorem covered_card (revealed : Disclosures) :
    (Finset.univ.filter (Covered revealed)).card =
      ∑ index : Instance, ∏ tree : Tree, (revealed index tree).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr (coveredEquiv revealed), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro index _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro tree _
  simp

theorem fresh_coverage (revealed : Disclosures) :
    Pr[Covered revealed | ($ᵗ View : ProbComp View)] =
      ((∑ index : Instance, ∏ tree : Tree, (revealed index tree).card : Nat) : ℝ≥0∞) /
        ((2 ^ 231 : Nat) : ℝ≥0∞) := by
  rw [probEvent_uniformSample, covered_card]
  have hcard : Fintype.card View = 2 ^ 231 := by
    norm_num [View, Instance, Tree, Leaf, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, totalHeight, forsHeight, forsTrees]
  rw [hcard]

/-- A deterministic sufficient condition on all disclosures. Each tree reveals at most
one new leaf per use of its FORS instance. The load bound itself is not assumed as security. -/
theorem fresh_coverage_le_of_loads (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 103) :
    Pr[Covered revealed | ($ᵗ View : ProbComp View)] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hcount : (∑ index : Instance, ∏ tree : Tree, (revealed index tree).card) ≤ 2 ^ 103 := by
    apply le_trans (Finset.sum_le_sum fun index _ => ?_) hmoment
    calc
      _ ≤ ∏ _ : Tree, loads index := Finset.prod_le_prod' (fun tree _ => hload index tree)
      _ = loads index ^ 14 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl
  rw [fresh_coverage]
  calc
    _ ≤ ((2 ^ 103 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

end SlhDsaSecurity.ForsCoverage

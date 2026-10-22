import SlhDsaSecurity.Proof.ForsLeaveOneOut

/-!
# Disclosures from one block of the tape, targets from the rest

`ForsLeaveOneOut.independent_tape_coverage_le` charges coverage on a tape whose coordinates
play both roles at once: every coordinate is a potential target, and every *other* coordinate
discloses. That ties the two counts together, and the load concentration then needs a cap on
the whole tape — which is what forces `trials ≤ 5 * 2 ^ 62` on the charge downstream.

The two roles are not the same in the game. Only a digest the signer randomised reveals a FORS
secret, and the signing limit caps those; a digest the adversary randomises for itself discloses
nothing and is capped by nothing. So the tape is split: its first `block` coordinates are the
disclosing ones and the rest are the targets, and `blockDisclosuresExcept` reads only the first
block. The cap is then needed only on `block`, while the number of targets stays free.

**The split is by index, and that is the point.** `ForsLeaveOneOut.coverage_le_of_full_cap`
resamples one coordinate and needs the disclosure set not to move, which an index-restricted set
satisfies by construction. A set selected by a predicate *computed from the run* would not:
resampling a coordinate can change which later coordinates the predicate selects, and
`hrevealed` would fail. Nothing else about the two roles needs to differ.

The block's own coordinates are a uniform tape of their own — the marginal of a uniform tape on
a set of coordinates — so the existing load concentration applies to them unchanged.
-/

open OracleComp OracleSpec ENNReal

noncomputable section

namespace SlhDsaSecurity.BlockDisclosures

open ForsDisclosureTape

/-! ## The block, as a tape of its own -/

/-- The first `block` coordinates of a tape, as a tape of their own. -/
def leftTape {block trials : Nat} (tape : Tape (block + trials)) : Tape block :=
  fun j => tape (Fin.castAdd trials j)

/-- The tape as its two blocks. -/
def splitBlocks (block trials : Nat) :
    Tape (block + trials) ≃ Tape block × Tape trials :=
  (Equiv.arrowCongr (finSumFinEquiv (m := block) (n := trials)).symm (Equiv.refl View)).trans
    (Equiv.sumArrowEquivProdArrow (Fin block) (Fin trials) View)

theorem splitBlocks_fst (block trials : Nat) (tape : Tape (block + trials)) :
    (splitBlocks block trials tape).1 = leftTape tape := rfl

/-- **The block is a uniform tape of its own.** -/
theorem evalDist_leftTape_uniform (block trials : Nat) :
    𝒟[leftTape <$> ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))] =
      𝒟[($ᵗ Tape block : ProbComp (Tape block))] := by
  have hmap : leftTape <$> ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials))) =
      Prod.fst <$> (splitBlocks block trials <$>
        ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))) := by
    rw [Functor.map_map]
    rfl
  rw [hmap, evalDist_map,
    evalDist_map_bijective_uniform_cross (α := Tape (block + trials))
      (splitBlocks block trials) (splitBlocks block trials).bijective,
    ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-- **The load concentration is needed only on the block.** -/
theorem block_bad_load_probability (block trials : Nat) (hblock : block ≤ 5 * 2 ^ 62) :
    Pr[fun tape : Tape (block + trials) => 2 ^ 103 < ∑ i, loads (leftTape tape) i ^ 14 |
      ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 := by
  rw [show (fun tape : Tape (block + trials) => 2 ^ 103 < ∑ i, loads (leftTape tape) i ^ 14) =
      (fun inner : Tape block => 2 ^ 103 < ∑ i, loads inner i ^ 14) ∘ leftTape from rfl,
    ← probEvent_map,
    probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_leftTape_uniform block trials)]
  exact bad_load_probability block hblock

/-! ## Disclosures from the block -/

/-- Disclosures taken from the first `block` coordinates only, with `excluded` left out. -/
def blockDisclosuresExcept {block trials : Nat} (excluded : Fin (block + trials))
    (tape : Tape (block + trials)) : ForsCoverage.Disclosures :=
  fun i tree =>
    (Finset.univ.filter (fun j : Fin block =>
        Fin.castAdd trials j ≠ excluded ∧ (tape (Fin.castAdd trials j)).1 = i)).image
      (fun j => (tape (Fin.castAdd trials j)).2 tree)

/-- **The block's disclosures are bounded by the block's own loads.** -/
theorem blockDisclosuresExcept_card_le_loads {block trials : Nat}
    (excluded : Fin (block + trials)) (tape : Tape (block + trials))
    (i : Instance) (tree : Tree) :
    (blockDisclosuresExcept excluded tape i tree).card ≤ loads (leftTape tape) i := by
  refine le_trans Finset.card_image_le (Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.2

/-- **The block's disclosures do not read the excluded coordinate.** -/
theorem blockDisclosuresExcept_update_self {block trials : Nat}
    (excluded : Fin (block + trials)) (tape : Tape (block + trials)) (value : View) :
    blockDisclosuresExcept excluded (Function.update tape excluded value) =
      blockDisclosuresExcept excluded tape := by
  funext i tree
  ext leaf
  simp only [blockDisclosuresExcept, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor <;> rintro ⟨j, ⟨hne, hi⟩, hleaf⟩ <;> refine ⟨j, ⟨hne, ?_⟩, ?_⟩
  · simpa only [Function.update_of_ne hne] using hi
  · simpa only [Function.update_of_ne hne] using hleaf
  · simpa only [Function.update_of_ne hne] using hi
  · simpa only [Function.update_of_ne hne] using hleaf

/-! ## The charge, with the two counts apart -/

/-- **Coverage by the block alone.** A causally selected coordinate has its fourteen FORS
leaves all disclosed by the block with probability at most `1 / 2 ^ 141` plus one unit of
`2 ^ -128` per selection — and the cap is on the block, not on the tape. -/
theorem block_coverage_le (block trials : Nat) (hblock : block ≤ 5 * 2 ^ 62)
    (policy : ForsAdaptiveTargets.Policy (block + trials)) :
    Pr[fun tape => ∃ j, policy j (ForsAdaptiveTargets.history tape j) = true ∧
        ForsCoverage.Covered (blockDisclosuresExcept j tape) (tape j) |
      ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        ForsAdaptiveTargets.expectedUses policy / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmain := ForsLeaveOneOut.coverage_le_of_full_cap policy blockDisclosuresExcept
    (fun tape => ∑ i, loads (leftTape tape) i ^ 14 ≤ 2 ^ 103)
    (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) blockDisclosuresExcept_update_self
    (fun tape hgood j => ForsCoverage.fresh_coverage_le_of_loads
      (blockDisclosuresExcept j tape) (loads (leftTape tape))
      (blockDisclosuresExcept_card_le_loads j tape) hgood)
  simp only [not_le] at hmain
  exact hmain.trans (add_le_add (block_bad_load_probability block trials hblock)
    (by simp only [div_eq_mul_inv, one_mul]; exact le_rfl))

/-! ## Selecting only targets

The policy is what decides how many coordinates are charged, and the block's coordinates are
not targets: a disclosing digest the forgery reads is the replay case, which the split sends
elsewhere. A policy that declines the block therefore spends at most the number of targets. -/

/-- **A policy that declines the block selects only target coordinates**, of which there are
`trials`. -/
theorem uses_le_of_declines_block {block trials : Nat}
    (policy : ForsAdaptiveTargets.Policy (block + trials))
    (hdeclines : ∀ (j : Fin (block + trials)) (past : Fin j.val → View),
      j.val < block → policy j past = false)
    (tape : Tape (block + trials)) : ForsAdaptiveTargets.uses policy tape ≤ trials := by
  classical
  have hsubset : (Finset.univ.filter
        (fun j => policy j (ForsAdaptiveTargets.history tape j) = true)) ⊆
      (Finset.univ.filter (fun j : Fin (block + trials) => ¬ j.val < block)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro hlt
    rw [hdeclines j (ForsAdaptiveTargets.history tape j) hlt] at hj
    exact Bool.false_ne_true hj
  refine le_trans (Finset.card_le_card hsubset) ?_
  have himage : (Finset.univ.filter (fun j : Fin (block + trials) => ¬ j.val < block)) ⊆
      Finset.image (Fin.natAdd block) (Finset.univ : Finset (Fin trials)) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hge := hj.2
    refine Finset.mem_image.mpr
      ⟨⟨j.val - block, by have := j.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    refine Fin.val_injective ?_
    simp only [Fin.natAdd]
    omega
  exact le_trans (Finset.card_le_card himage) (le_trans Finset.card_image_le
    (le_of_eq (Finset.card_univ.trans (Fintype.card_fin trials))))

/-- **A policy that declines the block spends at most the targets.** -/
theorem expectedUses_le_trials {block trials : Nat}
    (policy : ForsAdaptiveTargets.Policy (block + trials))
    (hdeclines : ∀ (j : Fin (block + trials)) (past : Fin j.val → View),
      j.val < block → policy j past = false) :
    ForsAdaptiveTargets.expectedUses policy ≤ (trials : ℝ≥0∞) := by
  classical
  calc ForsAdaptiveTargets.expectedUses policy
      ≤ ∑ tape : Tape (block + trials),
          Pr[= tape | ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))] *
            (trials : ℝ≥0∞) :=
        Finset.sum_le_sum fun tape _ =>
          mul_le_mul' le_rfl (Nat.cast_le.mpr (uses_le_of_declines_block policy hdeclines tape))
    _ = (∑ tape : Tape (block + trials),
          Pr[= tape | ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))]) *
            (trials : ℝ≥0∞) := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (trials : ℝ≥0∞) :=
        mul_le_mul' (le_trans (ENNReal.sum_le_tsum _) tsum_probOutput_le_one) le_rfl
    _ = _ := one_mul _

/-- **The charge with the counts apart.** The disclosing block pays the concentration failure
and nothing else; the targets pay one unit of `2 ^ -128` each. -/
theorem block_coverage_le_trials (block trials : Nat) (hblock : block ≤ 5 * 2 ^ 62)
    (policy : ForsAdaptiveTargets.Policy (block + trials))
    (hdeclines : ∀ (j : Fin (block + trials)) (past : Fin j.val → View),
      j.val < block → policy j past = false) :
    Pr[fun tape => ∃ j, policy j (ForsAdaptiveTargets.history tape j) = true ∧
        ForsCoverage.Covered (blockDisclosuresExcept j tape) (tape j) |
      ($ᵗ Tape (block + trials) : ProbComp (Tape (block + trials)))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + (trials : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (block_coverage_le block trials hblock policy)
    (add_le_add le_rfl (ENNReal.div_le_div_right
      (expectedUses_le_trials policy hdeclines) _))

end SlhDsaSecurity.BlockDisclosures

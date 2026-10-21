import SlhDsaSecurity.Statement.Parameters
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The assembly step for the 127-bit bound

The three contributions to the all-queries-counted bound combine exactly:

* the structural term costs `q / 2 ^ 128 = 2q / 2 ^ 129`;
* the FORS coverage term, routed through the sharper `2 ^ 102` load cap, costs
  `q / 2 ^ 129`;
* relating the actual honest disclosures to a capped set costs an additive `2 ^ -126 =
  8 / 2 ^ 129`.

Their sum is `(3q + 8) / 2 ^ 129`, and the target is `4q / 2 ^ 129`, so the bound holds
exactly when `3q + 8 ≤ 4q`, i.e. `q ≥ 8`. Charging every hash call makes that automatic:
key generation alone costs far more than eight hashes, and in any case an accepted forgery
forces at least 569 charged calls.

This also shows why the plain `2 ^ 103` load cap cannot be used. It would make the FORS term
`2q / 2 ^ 129`, giving a total of `4q / 2 ^ 129` with no room left for the additive term.
-/

open ENNReal

namespace SlhDsaSecurity.Assembly

theorem structural_eq (q : Nat) :
    (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) =
      ((2 * q : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  have hden : ((2 ^ 129 : Nat) : ℝ≥0∞) = 2 * ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    push_cast; ring
  rw [hden, Nat.cast_mul, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

theorem capFail_eq :
    1 / ((2 ^ 126 : Nat) : ℝ≥0∞) = ((8 : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  have hden : ((2 ^ 129 : Nat) : ℝ≥0∞) = 8 * ((2 ^ 126 : Nat) : ℝ≥0∞) := by
    push_cast; ring
  have hnum : ((8 : Nat) : ℝ≥0∞) = 8 * 1 := by norm_num
  rw [hden, hnum, ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

theorem target_eq (q : Nat) :
    (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) =
      ((4 * q : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  have hden : ((2 ^ 129 : Nat) : ℝ≥0∞) = 4 * ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    push_cast; ring
  rw [hden, Nat.cast_mul, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **The assembly step.** The structural term, the sharper FORS term and the additive cost
of capping the disclosures sum to at most the target once `q ≥ 8`. -/
theorem le_target_of_terms {advantage structural fors capFail : ℝ≥0∞} (q : Nat) (hq : 8 ≤ q)
    (hsplit : advantage ≤ structural + fors + capFail)
    (hstructural : structural ≤ (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hfors : fors ≤ (q : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞))
    (hcap : capFail ≤ 1 / ((2 ^ 126 : Nat) : ℝ≥0∞)) :
    advantage ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine hsplit.trans ?_
  rw [structural_eq q, capFail_eq, target_eq q] at *
  calc structural + fors + capFail
      ≤ ((2 * q : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) +
          ((8 : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
        exact add_le_add (add_le_add hstructural hfors) hcap
    _ = ((2 * q + q + 8 : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((4 * q : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
        omega

/-! ## The two-half assembly

The first-principles split is by *side* rather than by avenue, and it has only two terms, each
proved as a standalone charge:

* answer-side, `CombinedCharge.prob_combinedBad_within_le`, at `q / 2 ^ 128` — the structural
  and FORS clauses charged as one predicate, so their rate is the maximum `2 ^ -128` rather
  than the sum;
* input-side, `SecretGuessCharge.prob_secret_guessed_le`, at `q / 2 ^ 128` — the secret
  guesses staked by the queried inputs.

They sum to `2q / 2 ^ 128 = q / 2 ^ 127` exactly. Unlike `le_target_of_terms` there is no third
term and no additive slack: the bound is met with equality, which is the arithmetic statement
of the fact that a structural-class query really can buy both halves at once.
-/

theorem half_add_half (queries : Nat) :
    (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) =
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [ENNReal.div_add_div_same]
  have hden : ((2 ^ 128 : Nat) : ℝ≥0∞) = 2 * ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    push_cast; ring
  have hnum : (queries : ℝ≥0∞) + (queries : ℝ≥0∞) = 2 * (queries : ℝ≥0∞) := by ring
  rw [hden, hnum, ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **The two-half assembly.** An answer-side charge and an input-side charge, each at
`q / 2 ^ 128`, together meet the target exactly. -/
theorem le_target_of_halves {advantage answerSide inputSide : ℝ≥0∞} (queries : Nat)
    (hsplit : advantage ≤ answerSide + inputSide)
    (hanswer : answerSide ≤ (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : inputSide ≤ (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    advantage ≤ (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  hsplit.trans ((add_le_add hanswer hinput).trans_eq (half_add_half queries))

end SlhDsaSecurity.Assembly

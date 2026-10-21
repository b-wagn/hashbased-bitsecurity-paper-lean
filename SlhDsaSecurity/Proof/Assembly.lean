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

/-! ## Where the defects live: the message-class slack

`le_target_of_halves` meets the target with equality, so the defects incurred in discharging
the charges' hypotheses — the `2 ^ -126` load cap and the `2 ^ -165` format separation — have
nowhere to go. They are accommodated by charging the answer side *per class* instead of at its
maximum. In units of `2 ^ -129`, writing `qs` and `qm` for the structural- and message-class
query counts:

| | cost |
| --- | --- |
| target | `4 qs + 4 qm` |
| answer side | `2 qs + 1 qm` — rate `2` structurally, only `1` on a message input |
| input side | `2 qs + 2 qm` — a secret guess is available in either class |
| room left | `1 qm` |

So the message class carries exactly one unit of slack per query, and that is where the
defects are charged. It suffices: with `qm ≥ 16` the slack is `2 ^ -125`, which dominates
`2 ^ -126 + 2 ^ -165`; and with `qm < 16` there are at most fifteen disclosures, so
`∑ i loads i ^ 14 ≤ 15 ^ 14 < 2 ^ 55`, far under the `2 ^ 102` cap, which therefore holds
deterministically and incurs no defect at all.
-/

/-- **The per-class assembly.** Charging the answer side at its true per-class rate leaves one
unit of room per message-class query, and the three terms still meet the target exactly. -/
theorem le_target_of_classes {advantage answerSide inputSide defect : ℝ≥0∞}
    (structuralQueries messageQueries : Nat)
    (hsplit : advantage ≤ answerSide + inputSide + defect)
    (hanswer : answerSide ≤
      ((2 * structuralQueries + messageQueries : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞))
    (hinput : inputSide ≤
      ((2 * (structuralQueries + messageQueries) : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞))
    (hdefect : defect ≤ ((messageQueries : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞)) :
    advantage ≤
      ((structuralQueries + messageQueries : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine hsplit.trans ?_
  refine le_trans (add_le_add (add_le_add hanswer hinput) hdefect) ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, target_eq,
    ← Nat.cast_add, ← Nat.cast_add]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  omega

/-! ## The cap defect fits the slack, in both branches

`le_target_of_classes` leaves one unit of room per message-class query for the defects, and
the load cap is the expensive one. Both branches of the dichotomy are now available:

* `qm ≥ 16` — `ForsLeaveOneOut.independent_tape_coverage_le_sharper` bounds the coverage
  event by `1 / 2 ^ 126 + expectedUses / 2 ^ 129`, the first term being the cap defect;
* `qm < 16` — `ForsCoverageTerm.moment_le_of_few_digests` establishes the cap outright, at
  fewer than sixteen disclosures, so there is no defect at all.

The lemma below is the join: in either branch the defect is within `qm / 2 ^ 129`. The
threshold is what makes it work — `1 / 2 ^ 126` is `8 / 2 ^ 129`, and sixteen message-class
queries buy `16 / 2 ^ 129`, twice what is needed. -/

theorem defect_eq :
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) =
      ((8 : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  rw [show ((2 ^ 129 : Nat) : ℝ≥0∞) = 8 * ((2 ^ 126 : Nat) : ℝ≥0∞) from by push_cast; ring,
    show ((8 : Nat) : ℝ≥0∞) = 8 * 1 from by norm_num,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **The load-cap defect fits the message-class slack.** -/
theorem cap_defect_within_slack {defect : ℝ≥0∞} (messageQueries : Nat)
    (hsmall : messageQueries < 16 → defect = 0)
    (hlarge : 16 ≤ messageQueries → defect ≤ (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞)) :
    defect ≤ (messageQueries : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  rcases lt_or_ge messageQueries 16 with hcase | hcase
  · rw [hsmall hcase]
    exact zero_le
  · refine (hlarge hcase).trans ?_
    rw [defect_eq]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

end SlhDsaSecurity.Assembly

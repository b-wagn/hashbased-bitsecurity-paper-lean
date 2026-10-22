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

/-! ## The dichotomy, read off the weighted counter

The answer side is charged `weighted / 2 ^ 129`, against an allowance of `2 q / 2 ^ 129`. The
room left is `(2 q - weighted) / 2 ^ 129`, and the load-cap defect has to come out of it.

What makes this work without a second counter is that the same quantity bounds the number of
message-class queries. Writing `s` and `m` for the structural and message counts, the weights
are `2` and `1`, so `weighted = 2 s + m` while the total is `s + m ≤ q`; hence

    m ≤ 2 q - weighted.

So the case split can be made on `2 q - weighted`, which the instrumented run produces
directly:

* `2 q - weighted ≥ 16` — the room is at least `16 / 2 ^ 129 = 2 ^ -125`, twice the `2 ^ -126`
  defect, so the concentration bound is affordable;
* `2 q - weighted < 16` — then `m < 16`, fewer than sixteen disclosures, and
  `ForsCoverageTerm.moment_le_of_few_digests` gives the cap outright with no defect to pay.
-/

/-- **The message count is bounded by the room left in the weighted budget.** -/
theorem messageCount_le_slack (structural message queries : Nat)
    (htotal : structural + message ≤ queries) :
    message ≤ 2 * queries - (2 * structural + message) := by omega

/-- Either there is room for the defect, or there were too few disclosures to need one. -/
theorem slack_or_few (weighted message queries : Nat)
    (hbound : message ≤ 2 * queries - weighted) :
    16 ≤ 2 * queries - weighted ∨ message < 16 := by omega

/-- The allowance, in the units the weighted charge produces. -/
theorem target_eq_half (queries : Nat) :
    (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) =
      ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) := by
  rw [show ((2 ^ 129 : Nat) : ℝ≥0∞) = 2 * ((2 ^ 128 : Nat) : ℝ≥0∞) from by push_cast; ring,
    show ((2 * queries : Nat) : ℝ≥0∞) = 2 * (queries : ℝ≥0∞) from by push_cast; ring,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]

/-- **With room, the charge and the defect together stay inside the allowance.** -/
theorem weighted_add_defect_le (weighted queries : Nat)
    (hslack : 16 ≤ 2 * queries - weighted) (hle : weighted ≤ 2 * queries) :
    (weighted : ℝ≥0∞) / ((2 ^ 129 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) ≤
      (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [defect_eq, ENNReal.div_add_div_same, ← Nat.cast_add, target_eq_half]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  omega

/-! ## The accounting the finished proof has to meet

The halves as they now stand are not `q / 2 ^ 128` each. Both are smaller by the honest
phase's own hashing, which is charged to `q` and can buy nothing — key generation spends at
least `2 ^ subtreeHeight = 512` calls while leaving the walk's cache untouched. The input half
is larger by the forgery's claimed cells, charged as candidates so that "output an unavailable
cell without ever querying for it" needs no separate argument; there are `forsTrees +
layers * chains = 259` of them. And the answer half carries the coverage tape's `2 ^ -141`, the
load cap's `2 ^ -126`, and the input-format coincidence's `2 ^ -165`.

So the sum to check is

    (q - 512 + 259) / 2 ^ 128 + (q - 512) / 2 ^ 128 + (2 ^ -126 + 2 ^ -141 + 2 ^ -165)
      ≤ q / 2 ^ 127

and it holds with room: the two counts give `2 q - 765`, the defects are under `5 / 2 ^ 128`,
and `2 q - 760 ≤ 2 q`. The margin is `760` units where `5` are needed, which is the point of
charging every hash call — the honest phase pays for the defects many times over.

`le_target_of_counts` is that, with the constants as parameters so the arithmetic does not have
to be redone if a count moves. -/

private theorem cast_pow (k : Nat) : ((2 ^ k : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by
  push_cast; ring

/-- A fraction over `2 ^ j` rewritten over a larger power of two. -/
private theorem div_pow_eq (m j k : Nat) (hjk : j ≤ k) :
    ((m : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ j =
      ((m * 2 ^ (k - j) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ k := by
  have hsplit : (2 : ℝ≥0∞) ^ k = (2 : ℝ≥0∞) ^ (k - j) * (2 : ℝ≥0∞) ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hnum : ((m * 2 ^ (k - j) : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (k - j) * (m : ℝ≥0∞) := by
    push_cast; ring
  rw [hsplit, hnum, ENNReal.mul_div_mul_left _ _ (by positivity) (by simp)]

/-- Three small defects cost under five units of `2 ^ -128`. -/
theorem defects_le_five :
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) ≤
      ((5 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [cast_pow, cast_pow, cast_pow, cast_pow,
    show (1 : ℝ≥0∞) = ((1 : Nat) : ℝ≥0∞) from by push_cast; ring,
    div_pow_eq 1 126 165 (by norm_num), div_pow_eq 1 141 165 (by norm_num),
    div_pow_eq 1 165 165 (by norm_num), div_pow_eq 5 128 165 (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  rw [← Nat.cast_add, ← Nat.cast_add]
  refine ENNReal.div_le_div_right ?_ _
  exact Nat.cast_le.mpr (by norm_num)

/-- **Four small defects cost under six units of `2 ^ -128`.** The fourth is the coincidence
`SK.prf = PK.seed`, which is what the `PRF_msg` class separation excludes: a canonical input
begins with the public seed and a `PRF_msg` input with the PRF seed, so unless the two agree no
query is in both classes and the two charges share one record rather than doubling it. -/
theorem defects_le_six :
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
      ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [cast_pow, cast_pow, cast_pow, cast_pow,
    show (1 : ℝ≥0∞) = ((1 : Nat) : ℝ≥0∞) from by push_cast; ring,
    div_pow_eq 1 126 165 (by norm_num), div_pow_eq 1 141 165 (by norm_num),
    div_pow_eq 1 165 165 (by norm_num), div_pow_eq 1 128 165 (by norm_num),
    div_pow_eq 6 128 165 (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  refine ENNReal.div_le_div_right ?_ _
  exact Nat.cast_le.mpr (by norm_num)

/-- **A defect proportional to the served requests, added to the four constant ones.** -/
theorem defects_add_served_le (served : Nat) :
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (served : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
      ((6 + served : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  calc (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (served : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)
      ≤ ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (served : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr; exact defects_le_six
    _ = _ := by rw [ENNReal.div_add_div_same, ← Nat.cast_add]

/-! ## Two slacks

The halves no longer spend the same room. Key generation's `2 ^ subtreeHeight` is reserved on
both, but the signer's own hashing is reserved only where the record is counted, so the counts
the two halves are measured against differ. What the allowance has to meet is unchanged in
substance: the forgery's claimed cells and the defects together must fit inside the two reserves
put together. -/

/-- **The target, from two counts reserving different amounts and a defect allowance.** -/
theorem le_target_of_two_slacks (queries inputSlack answerSlack extra defectUnits : Nat)
    (hinput : inputSlack ≤ queries) (hanswer : answerSlack ≤ queries)
    (hfits : extra + defectUnits ≤ inputSlack + answerSlack)
    (defect : ℝ≥0∞)
    (hdefect : defect ≤ (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - inputSlack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - answerSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hsum : (queries - inputSlack + extra) + (queries - answerSlack) + defectUnits ≤
      2 * queries := by omega
  calc ((queries - inputSlack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - answerSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect
      ≤ ((queries - inputSlack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((queries - answerSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr
    _ = (((queries - inputSlack + extra) + (queries - answerSlack) + defectUnits : Nat) :
          ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _
    _ = (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
        rw [show ((2 * queries : Nat) : ℝ≥0∞) = (queries : ℝ≥0∞) + (queries : ℝ≥0∞) from by
          push_cast; ring, ← ENNReal.div_add_div_same, half_add_half]

/-- **The accounting with the signer's spend reserved.** The forgery's two hundred and
fifty-nine claimed cells and six constant defects, plus one defect unit per served request,
against key generation's five hundred and twelve reserved on both halves and one more per
served request reserved on the half that counts the record. -/
theorem le_target_of_served (queries served : Nat) (hkeygen : 2 ^ subtreeHeight + served ≤ queries)
    (defect : ℝ≥0∞)
    (hdefect : defect ≤ ((6 + served : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - (2 ^ subtreeHeight + served) + 259 : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine le_target_of_two_slacks queries (2 ^ subtreeHeight + served) (2 ^ subtreeHeight) 259
    (6 + served) hkeygen (by omega) ?_ defect hdefect
  simp only [subtreeHeight]
  omega

/-- **The target, from the two counts and a defect allowance.** -/
theorem le_target_of_counts (queries slack extra defectUnits : Nat)
    (hslack : slack ≤ queries) (hfits : extra + defectUnits ≤ 2 * slack)
    (defect : ℝ≥0∞)
    (hdefect : defect ≤ (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - slack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hsum : (queries - slack + extra) + (queries - slack) + defectUnits ≤ 2 * queries := by
    omega
  calc ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - slack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect
      ≤ ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((queries - slack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr
    _ = (((queries - slack + extra) + (queries - slack) + defectUnits : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _
    _ = (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
        rw [show ((2 * queries : Nat) : ℝ≥0∞) = (queries : ℝ≥0∞) + (queries : ℝ≥0∞) from by
          push_cast; ring, ← ENNReal.div_add_div_same, half_add_half]

end SlhDsaSecurity.Assembly

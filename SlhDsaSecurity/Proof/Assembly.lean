import SlhDsaSecurity.Statement.Parameters
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The assembly step for the 127-bit bound

**The live ledger is `le_target_of_full`, and it is the only one of the five in this file that
has a consumer.** `Target.allowanceOf` applies it, and its whole content is the `Nat` line

    (q - slack + extra) + q + defectUnits ≤ 2 * q

at `slack = 2 ^ subtreeHeight = 512` (key generation's own hashing, reserved on the input half),
`extra = claims` (the forgery's claimed cells, `259` at the live instantiation) and
`defectUnits = 6` (`defects_le_six`, covering the load cap at `2 ^ -126`, the coverage tape at
`2 ^ -141`, the seed coincidence at `2 ^ -128` and the input-format coincidence at `2 ^ -165`).
So what has to hold is `claims + 6 ≤ 512`, and at `claims = 259` the margin is **247** units of
`2 ^ -128`.

The `q` coefficient has **no** margin: the same line is `2 * q` on the right and `q + q` on the
left, one per half. A third `q`-proportional term cannot be added anywhere, whatever constant it
carries. Constants can, up to the 247.

## The four earlier ledgers, and why they are still here

This file accumulated a ledger per design generation, and **four of the five are now unconsumed**.
They are kept because each is true and cheap to re-reach for, and named here because a reader who
takes the wrong one gets a margin that is wrong by a factor of three.

| theorem | shape | consumers |
| --- | --- | --- |
| `le_target_of_terms` | three terms, `3q + 8 ≤ 4q`, needs `q ≥ 8` | none |
| `le_target_of_halves` | two halves at `q / 2 ^ 128`, met with equality | none |
| `le_target_of_two_slacks` | the two halves reserve different amounts | none |
| `le_target_of_served` | `two_slacks` with the signer's spend reserved | none |
| `le_target_of_counts` | both halves reserve `slack`, so `extra + defectUnits ≤ 2 * slack` | none |
| **`le_target_of_full`** | **the answer half spends the whole `q`; `extra + defectUnits ≤ slack`** | **`Target.allowanceOf`** |
| `le_target_doubled` | the shared half carries two records; target `3q / 2 ^ 128` | none — the fallback |

The `759`/`1024`-style figures that appear in older notes belong to `le_target_of_counts` and
`le_target_of_two_slacks`, which reserve on *both* halves. `le_target_of_full` reserves on one,
which is why its margin is 247 and not 759.
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

/-- **The assembly step, first generation.** The structural term, a FORS term at
`q / 2 ^ 129` and the additive cost of capping the disclosures sum to at most the target once
`q ≥ 8`.

*Currently unconsumed.* It belongs to a design in which the FORS coverage term was
`q`-proportional at half the structural rate, which is what the `2 ^ 102` cap buys
(`ForsConcentrationSharper`, additive `2 ^ -126`). The header's remark that the `2 ^ 103` cap
"cannot be used" is about **that** term and is correct about it.

**Both caps are live, for different terms, and the remark should not be read as a prohibition.**
`2 ^ 102` is the sharper one and is what `CombinedCharge`, `WholeGameStructural` and
`WarmedCharges` take as `hmoment`; `2 ^ 103` is the coverage tape's, where
`BlockViews.GoodBlock` is `∑ loads ^ 14 ≤ 2 ^ 103` and `BlockViews.prob_not_goodBlock_le` turns
it into the flat `2 ^ -141` the live coverage charge spends. The live coverage clause is not
`q`-proportional at all, so the trade-off this ledger describes does not arise for it. -/
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
`q / 2 ^ 128`, together meet the target exactly.

*Currently unconsumed:* meeting the target with equality leaves nowhere for the defects, which is
what the sections below are about. `half_add_half`, the arithmetic underneath it, **is** live. -/
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

/-! ## An accounting that reserves on both halves

**This is not the accounting the finished proof meets** — that is `le_target_of_full`, under
*The accounting the finished proof does meet* below. `le_target_of_counts` is kept because it is
the honest ledger for a design in which both halves subtract key generation's spend, and because
its arithmetic is what the `759`-unit margin in older notes refers to.

The halves as they stand in *that* design are not `q / 2 ^ 128` each. Both are smaller by the honest
phase's own hashing, which is charged to `q` and can buy nothing — key generation spends at
least `2 ^ subtreeHeight = 512` calls while leaving the walk's cache untouched. The input half
is larger by the forgery's claimed cells, charged as candidates so that "output an unavailable
cell without ever querying for it" needs no separate argument; there are `forsTrees +
layers * chains = 259` of them. And the answer half carries the coverage tape's `2 ^ -141`, the
load cap's `2 ^ -126`, and the input-format coincidence's `2 ^ -165`.

So the sum to check is

    (q - 512 + 259) / 2 ^ 128 + (q - 512) / 2 ^ 128 + (2 ^ -126 + 2 ^ -141 + 2 ^ -165)
      ≤ q / 2 ^ 127

and it holds with room: the two counts give `2 q - 765`, the three defects are under
`5 / 2 ^ 128` (`defects_le_five`), and `2 q - 760 ≤ 2 q`. The margin is `760` units where `5` are
needed.

Both numerals are of this design and not of the live one. The live defect sum has a **fourth**
term, the seed coincidence, and is bounded by `defects_le_six`; and the live margin is 247,
because `le_target_of_full` reserves on one half rather than two.

`le_target_of_counts` is this, with the constants as parameters so the arithmetic does not have
to be redone if a count moves. *Currently unconsumed.* -/

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

/-- Three small defects cost under five units of `2 ^ -128`.

*Currently unconsumed.* The live defect sum has a fourth term — the seed coincidence, at
`2 ^ -128` — and is `defects_le_six`, which `Target.allowanceOf` uses. -/
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
theorem defects_add_served_le (units : Nat) :
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (units : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
      ((6 + units : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  calc (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (units : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)
      ≤ ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (units : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr; exact defects_le_six
    _ = _ := by rw [ENNReal.div_add_div_same, ← Nat.cast_add]

/-! ## Two slacks

The halves no longer spend the same room. Key generation's `2 ^ subtreeHeight` is reserved on
both, but the signer's own hashing is reserved only where the record is counted, so the counts
the two halves are measured against differ. What the allowance has to meet is unchanged in
substance: the forgery's claimed cells and the defects together must fit inside the two reserves
put together. -/

/-- **The target, from two counts reserving different amounts and a defect allowance.**

*Currently unconsumed*, with `le_target_of_served` below it. -/
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
served request reserved on the half that counts the record.

*Currently unconsumed.* -/
theorem le_target_of_served (queries served : Nat)
    (hkeygen : 2 ^ subtreeHeight + 2 * served ≤ queries) (defect : ℝ≥0∞)
    (hdefect : defect ≤ ((6 + 2 * served : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - (2 ^ subtreeHeight + 2 * served) + 259 : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((queries - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine le_target_of_two_slacks queries (2 ^ subtreeHeight + 2 * served) (2 ^ subtreeHeight) 259
    (6 + 2 * served) hkeygen (by omega) ?_ defect hdefect
  simp only [subtreeHeight]
  omega

/-- **The target, from the two counts and a defect allowance.** *Currently unconsumed*; see the
section above for which design it belongs to. -/
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

/-! ## The accounting the finished proof does meet

`Target.allowanceOf` calls `le_target_of_full` and nothing else in this file, so this is the
ledger the 127-bit bound actually rests on. It differs from every accounting above in one
respect, and the difference is the whole of why its margin is 247 rather than 759: **only the
input half subtracts key generation's spend.** The answer half is charged the entire `q`.

So the `Nat` line is `(q - slack + extra) + q + defectUnits ≤ 2 * q`, which for `slack ≤ q` is
`extra + defectUnits ≤ slack` — a single reserve, `512`, against `claims + 6`. At `claims = 259`
that leaves 247 units of `2 ^ -128` for any further constant, and nothing at all for a further
`q`-proportional term.

`Target.allowanceOf` keeps `claims` a parameter for exactly that reason: a caller with a constant
charge raises the numeral and the inequality still holds, while a caller with a `q`-shaped charge
finds it cannot, at the call site rather than three files away. -/

/-- **The target, with the answer side charged the whole count.** The reserve the other side
keeps is what pays for it: the answer half never has to subtract key generation's own hashes,
because the input half's `slack` already covers the extra and the defects.

**This is the live ledger**, applied by `Target.allowanceOf`. -/
theorem le_target_of_full (queries slack extra defectUnits : Nat)
    (hslack : slack ≤ queries) (hfits : extra + defectUnits ≤ slack)
    (defect : ℝ≥0∞)
    (hdefect : defect ≤ (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hsum : (queries - slack + extra) + queries + defectUnits ≤ 2 * queries := by omega
  calc ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect
      ≤ ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr
    _ = (((queries - slack + extra) + queries + defectUnits : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _
    _ = (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
        rw [show ((2 * queries : Nat) : ℝ≥0∞) = (queries : ℝ≥0∞) + (queries : ℝ≥0∞) from by
          push_cast; ring, ← ENNReal.div_add_div_same, half_add_half]

/-! ## The fallback ledger, if the shared half has to carry two records

`le_target_of_full` gives the shared half one record's worth. If the `PRF_msg` column cannot be
bounded in the real order — `PrfClassCount.expected_card_filter_prfClass_le` proves the count
below one entry's worth only with the seed drawn **after** the record, and in the real order the
bound is false — then what is available is `TargetColumn.expected_three_parts_le_two_budgets`,
two records' worth, and the line below is the one that closes.

**It does not close against `q / 2 ^ 127`, and that is the whole content of the fallback.** With
`2 * (q - slack)` on the shared side the left is `3q` at best, so the target it meets is
`3 * q / 2 ^ 128`, which is `q / 2 ^ 126.415…`. `doubled_le_126` rounds that to `q / 2 ^ 126`,
which is the number to quote if this line becomes live.

**Which line is live is decided by one question** — whether the assembly needs
`E[card recordPrfClass]` in the real order, or only `Pr[RecordMeetsPrfClass]`. Only the event:
`Target.allowanceWithPrfUnit` stands and this is unused. The count: this is the line, and
`q₀ ≈ 2 ^ 68` is the alternative to it rather than a rival.

**Nothing is instantiated at this line.** It is stated so that the answer, whichever it is,
does not wait on arithmetic. -/

/-- **The ledger with the shared half carrying two records.** The `Nat` line is
`2 * (q - slack) + extra + q + defectUnits ≤ 3 * q`, which for `slack ≤ q` is
`extra + defectUnits ≤ 2 * slack` — twice the room of `le_target_of_full`, against a target one
factor of `3 / 2` weaker. -/
theorem le_target_doubled (queries slack extra defectUnits : Nat)
    (hslack : slack ≤ queries) (hfits : extra + defectUnits ≤ 2 * slack)
    (defect : ℝ≥0∞)
    (hdefect : defect ≤ (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((2 * (queries - slack) + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect ≤
      ((3 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hsum : (2 * (queries - slack) + extra) + queries + defectUnits ≤ 3 * queries := by omega
  calc ((2 * (queries - slack) + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect
      ≤ ((2 * (queries - slack) + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr
    _ = (((2 * (queries - slack) + extra) + queries + defectUnits : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((3 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _

/-- **And `3 * q / 2 ^ 128` is inside `q / 2 ^ 126`**, which is the roundable form. The sharp
value is `q / 2 ^ 126.415…`; the rounding spends the difference rather than earning it. -/
theorem doubled_le_126 (queries : Nat) :
    ((3 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
      (queries : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) := by
  have hfour : (queries : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) =
      ((4 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    have hden : ((2 ^ 128 : Nat) : ℝ≥0∞) = 4 * ((2 ^ 126 : Nat) : ℝ≥0∞) := by
      push_cast; ring
    rw [hden, Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
  rw [hfour]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

end SlhDsaSecurity.Assembly

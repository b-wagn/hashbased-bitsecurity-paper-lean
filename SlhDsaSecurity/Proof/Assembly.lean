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
| **`le_target_doubled`** | **the shared half carries two records; target `3q / 2 ^ 128`** | **`Target.allowanceDoubled` — the live line** |

The `759`/`1024`-style figures that appear in older notes belong to `le_target_of_counts` and
`le_target_of_two_slacks`, which reserve on *both* halves. `le_target_of_full` reserves on one,
which is why its margin is 247 and not 759.
-/

open ENNReal

namespace SlhDsaSecurity.Assembly

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

/-! ## Two slacks

The halves no longer spend the same room. Key generation's `2 ^ subtreeHeight` is reserved on
both, but the signer's own hashing is reserved only where the record is counted, so the counts
the two halves are measured against differ. What the allowance has to meet is unchanged in
substance: the forgery's claimed cells and the defects together must fit inside the two reserves
put together. -/

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

/-! ## The ledger the shared half actually needs: two records

`le_target_of_full` gives the shared half one record's worth. If the `PRF_msg` column cannot be
bounded in the real order — `PrfClassCount.expected_card_filter_prfClass_le` proves the count
below one entry's worth only with the seed drawn **after** the record, and in the real order the
bound is false — then what is available is `TargetColumn.expected_three_parts_le_two_budgets`,
two records' worth, and the line below is the one that closes.

**It does not close against `q / 2 ^ 127`, and that is the whole content of the fallback.** With
`2 * (q - slack)` on the shared side the left is `3q` at best, so the target it meets is
`3 * q / 2 ^ 128`, which is `q / 2 ^ 126.415…`. `doubled_le_126` rounds that to `q / 2 ^ 126`,
which is the number to quote if this line becomes live.

**That question is settled and this is the line.** The assembly charges each clause at
`expected count / 2 ^ 128` and sums the counts against the budget, so the seed clause's count
must be record-sized — the union bound gives `Pr[seed event] ≤ card record / 2 ^ 128` and
nothing better. The `PRF_msg` part is *below one*, and charging the clause at that count would
force the seed event to be empty, which is `TargetColumn.seedEvent_empty_of_prfClass_charge`.
**Being small is what disqualifies it.** -/

end SlhDsaSecurity.Assembly

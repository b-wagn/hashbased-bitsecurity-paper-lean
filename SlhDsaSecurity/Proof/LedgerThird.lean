import SlhDsaSecurity.Proof.Assembly
import SlhDsaSecurity.Proof.ClassExpectation

/-!
# What a third column would have to cost

`Assembly.le_target_of_full` is the live ledger and its `Nat` line is

    (q - slack + extra) + q + defectUnits ≤ 2 * q

with `slack = 512`, `extra = 259` and `defectUnits = 6`, so the left side is `2 * q - 247`. The
`q` coefficient has no margin; what margin there is, is **247 units of `2 ^ -128` and it is a
constant**.

This file answers one question and nothing else: *can the line carry a third term at all, and
at what size?* The first theorem is the line with a third column added, which says exactly what
such a column must meet — `extra + defectUnits + thirdUnits ≤ slack`, i.e. at the live
instantiation `thirdUnits ≤ 247`. The second is the arithmetic that kills a `q`-dependent
column: a term of size `q ^ 2 / 2 ^ 256` is `q ^ 2 / 2 ^ 128` units, and at `q = 2 ^ 68` that is
`256`, which does not fit in `247`.

**So a third column is admissible exactly when its unit count is bounded by a constant.** A
second-order term is not second-order *here*: `q ^ 2 / 2 ^ 256` is small against the target
`q / 2 ^ 127` only in the sense `q ≤ c · 2 ^ 128`, and the ledger's slack is not `c · q` but
`247`. The inequality the route needs is `q ^ 2 ≤ 247 · 2 ^ 128`, which is `q ≲ 2 ^ 67.97` — not
a restatement away, since that *is* the underlying real-number inequality and not an artefact of
the `Nat` accounting.
-/

open ENNReal OracleComp OracleSpec

namespace SlhDsaSecurity.LedgerThird

/-- **The ledger with a third column.** `Assembly.le_target_of_full` with one more term, and the
only thing that changes is what the fits hypothesis has to absorb. -/
theorem le_target_of_full_third (queries slack extra defectUnits thirdUnits : Nat)
    (hslack : slack ≤ queries) (hfits : extra + defectUnits + thirdUnits ≤ slack)
    (defect third : ℝ≥0∞)
    (hdefect : defect ≤ (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hthird : third ≤ (thirdUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect + third ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hsum : (queries - slack + extra) + queries + (defectUnits + thirdUnits) ≤ 2 * queries := by
    omega
  calc ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defect + third
      ≤ ((queries - slack + extra : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (queries : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (defectUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (thirdUnits : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by gcongr
    _ = (((queries - slack + extra) + queries + (defectUnits + thirdUnits) : Nat) : ℝ≥0∞) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        push_cast
        ring_nf
    _ ≤ ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _
    _ = (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
        rw [show ((2 * queries : Nat) : ℝ≥0∞) = (queries : ℝ≥0∞) + (queries : ℝ≥0∞) from by
          push_cast; ring, ← ENNReal.div_add_div_same, Assembly.half_add_half]

/-- **And a `q ^ 2`-sized column does not meet it.** At the live instantiation the fits
hypothesis is `259 + 6 + thirdUnits ≤ 512`, so `thirdUnits ≤ 247`; a column of size
`q ^ 2 / 2 ^ 256` carries `q ^ 2 / 2 ^ 128` units, and one value of `q` is enough to refuse it.

Stated at `2 ^ 68` because that is where it first fails: `2 ^ 136 / 2 ^ 128 = 256`. -/
theorem q_squared_third_not_fits :
    ¬ (259 + 6 + (2 ^ 68 : Nat) * (2 ^ 68 : Nat) / (2 ^ 128 : Nat) ≤ 512) := by
  norm_num

/-- **The same, as the inequality the route would have to prove instead.** The margin is a
constant and the column is not, so what is needed is a bound on `q` — and `247 * 2 ^ 128` is
`q ≲ 2 ^ 67.97`, far below the scale the statement is read at. -/
theorem q_squared_third_fits_iff (queries : Nat) :
    259 + 6 + queries * queries / (2 ^ 128 : Nat) ≤ 512 ↔
      queries * queries / (2 ^ 128 : Nat) ≤ 247 := by
  omega


/-! ## The indicator step, which is sound on its own

The route that would have made a third column small reads: the count vanishes off an event, so
its expectation is at most a bound on the count times the event's probability. That step is
**correct** and is proved here, because it is worth separating a sound step from the arithmetic
that refuses its conclusion — the step is pathwise domination and involves no independence, so
the correlation between the indicator and the count is irrelevant to it.

What refuses the route is the line above, not this. -/

open scoped Classical in
/-- **A count that vanishes off an event is bounded by that event's probability**, times
whatever bounds the count on it. -/
theorem expected_le_mul_probEvent {β : Type} (run : ProbComp β) (count : β → Nat) (bound : Nat)
    (S : β → Prop) (hbound : ∀ v ∈ support run, count v ≤ bound)
    (hzero : ∀ v ∈ support run, ¬ S v → count v = 0) :
    ClassExpectation.expected run count ≤ (bound : ℝ≥0∞) * Pr[S | run] := by
  classical
  rw [ClassExpectation.expected, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases hmem : value ∈ support run
  · by_cases hS : S value
    · rw [if_pos hS, mul_comm (bound : ℝ≥0∞)]
      exact mul_le_mul_right (Nat.cast_le.mpr (hbound value hmem)) _
    · rw [hzero value hmem hS]
      simp
  · rw [probOutput_eq_zero_of_not_mem_support hmem]
    simp



/-! ## The exact threshold

`Target.allowanceOf` takes `claims + 6 ≤ 2 ^ subtreeHeight`, so with `subtreeHeight = 9` the
`claims` column admits at most `506`, of which `259` is already spoken for by the forgery's
claimed cells. **The spare is exactly `247` units of `2 ^ -128`, and it is a constant.**

The `PRF_msg` column's size on the route under consideration is `(q - 2 ^ 9) ^ 2 / 2 ^ 128`
units — the record bounds the count on the seed event, the seed event is charged at the record
over `2 ^ 128`, and the record is `q - 2 ^ 9`. So the line closes exactly when

    (q - 2 ^ 9) ^ 2 ≤ 247 * 2 ^ 128

and the two theorems below pin the largest `q` for which it does. `q₀` is
`289913339861193349628`, which is about `2 ^ 67.974`.

**At `q₀` the ledger is saturated**: the `claims` column is `259 + 247 = 506` and
`506 + 6 = 512 = 2 ^ subtreeHeight` with nothing spare. There is no margin left to absorb a
later correction, which is worth knowing before the number is quoted. -/

/-- **The spare in the `claims` column is 247 units**, at the live `claims = 259`. -/
theorem claims_spare : (259 : Nat) + 247 + 6 ≤ 2 ^ subtreeHeight := by
  norm_num [subtreeHeight]

/-- **And it is spent exactly**: one more unit does not fit. -/
theorem claims_spare_exact : ¬ ((259 : Nat) + 248 + 6 ≤ 2 ^ subtreeHeight) := by
  norm_num [subtreeHeight]

/-- **The threshold, below.** At `q₀ = 289913339861193349628` the `PRF_msg` column still fits in
the 247 spare units. -/
theorem q_squared_fits_at_threshold :
    (289913339861193349628 - 2 ^ subtreeHeight) *
        (289913339861193349628 - 2 ^ subtreeHeight) ≤ 247 * 2 ^ 128 := by
  norm_num [subtreeHeight]

/-- **And above.** At `q₀ + 1` it does not, so `q₀` is the largest budget this route reaches. -/
theorem q_squared_not_fits_above_threshold :
    ¬ ((289913339861193349629 - 2 ^ subtreeHeight) *
        (289913339861193349629 - 2 ^ subtreeHeight) ≤ 247 * 2 ^ 128) := by
  norm_num [subtreeHeight]

/-- **The ledger closes at the saturated column.** `Target.allowanceOf`'s hypothesis at
`claims = 506`, which is `259` for the cells and `247` for the `PRF_msg` column. -/
theorem allowance_hypothesis_at_saturation : (506 : Nat) + 6 ≤ 2 ^ subtreeHeight := by
  norm_num [subtreeHeight]



/-! ## And at one unit, which is what the summed count actually costs

`PrfClassCount.expected_card_filter_prfClass_le` bounds the expected class count by
`card record / 2 ^ 128` rather than by `card record ^ 2 / 2 ^ 128` — the entries are summed
instead of union-bounded. At `card record ≤ q - 2 ^ subtreeHeight` that is **below one entry's
worth** for every budget up to `2 ^ 128`, so the column costs a single unit of the `claims`
budget and the ledger closes with 246 spare.

**That removes the threshold entirely.** `q₀` above was a property of the lossy route, not of
the quantity: bounding the count by the record *before* taking the expectation is what squared
it. The theorems above are kept because they say what a `q`-dependent column would have cost,
which is the thing worth remembering.

**What is not removed is the order.** The summed bound is proved with the seed drawn *after*
the record, which is the blind order; in the real game the walk fixes the seed first and an
adversary may aim every query at it. So this discharges the column exactly when the blind-order
count transfers, and that transfer is the open hop — not an arithmetic question. -/

/-- **One unit covers the column**, for every budget the statement is read at. -/
theorem prf_column_within_one_unit (queries : Nat)
    (hq : queries - 2 ^ subtreeHeight ≤ 2 ^ 128) :
    ((queries - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤ 1 := by
  calc ((queries - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)
      ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
    _ = 1 := ENNReal.div_self (by positivity) (by simp)

/-- **And the ledger closes with 246 units spare**, against the 0 the quadratic column left. -/
theorem claims_spare_with_prf_unit : (259 : Nat) + 1 + 6 ≤ 2 ^ subtreeHeight := by
  norm_num [subtreeHeight]

/-- The spare, written out. -/
theorem claims_spare_with_prf_unit_margin :
    2 ^ subtreeHeight - ((259 : Nat) + 1 + 6) = 246 := by
  norm_num [subtreeHeight]


end SlhDsaSecurity.LedgerThird

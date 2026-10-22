import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.ClassExpectation

/-!
# How many of a record's entries are `PRF_msg` inputs at a seed drawn after it

`RandomizerGate.prob_run_randomizerInput_le` charges the **event** that some entry of the record
is a `PRF_msg` input at the drawn seed, at `card / 2 ^ 128`. What a ledger column needs is the
**expected count** of such entries, and the two are not the same quantity: the obvious route
from the event to the count — bound the count by the record on the event, multiply by the
event's probability — gives `card ^ 2 / 2 ^ 128`, because it bounds the count *before* taking
the expectation.

**Summing instead of union-bounding gives the count directly, and it is below one.** Each entry
lies in the class for at most one seed, since `RandomizerGate.prfGuess` recovers the seed from
the input; so each entry contributes at most `2 ^ -128` to the expectation, and the whole count
contributes at most `card / 2 ^ 128`. For any `card < 2 ^ 128` that is less than one entry's
worth — a genuinely `O(1)` column rather than an `O(q ^ 2 / 2 ^ 128)` one.

**The quadratic was an artefact of the route and not of the quantity.** Bounding a sum of small
things by a big thing times a small thing is the same shape of loss as a union bound that cannot
see a partition: both throw away the structure that makes the sum small, and both are visible
only once the sum is written out.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.PrfClassCount

open Security ClassExpectation

/-- **An indicator's expectation is its event's probability.** -/
theorem expected_indicator_eq {β : Type} (run : ProbComp β) (P : β → Prop)
    [DecidablePred P] :
    expected run (fun value => if P value then 1 else 0) = Pr[P | run] := by
  classical
  rw [expected, probEvent_eq_tsum_ite]
  refine tsum_congr fun value => ?_
  by_cases hP : P value
  · rw [if_pos hP, if_pos hP, Nat.cast_one, mul_one]
  · rw [if_neg hP, if_neg hP, Nat.cast_zero, mul_zero]

/-- **One entry is in the class for at most one seed**, so against a seed drawn afterwards it
is in the class with probability at most `2 ^ -128`. `RandomizerGate.prfGuess` is the function
that recovers the seed from the input, which is what makes "at most one" true. -/
theorem prob_prfClass_le (input : Bytes) :
    Pr[fun prf : Digest => RandomizerGate.PrfClass prf input |
      ($ᵗ Digest : ProbComp Digest)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono ?_)
    (le_of_eq (SecretGuessCharge.prob_single_guess (RandomizerGate.prfGuess input)))
  rintro prf - ⟨seed, message, rfl⟩
  exact RandomizerGate.prfGuess_randomizerInput prf seed message

open scoped Classical in
/-- **And so a record's expected class count is its size over `2 ^ 128`.** The entries are
summed rather than union-bounded, so nothing is lost to the count's size: each contributes its
own `2 ^ -128` and no more. -/
theorem expected_card_filter_prfClass_le (record : Multiset Bytes) :
    expected ($ᵗ Digest : ProbComp Digest)
        (fun prf => Multiset.card (record.filter (RandomizerGate.PrfClass prf))) ≤
      ((Multiset.card record : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  induction record using Multiset.induction_on with
  | empty => simp [expected]
  | cons entry rest ih =>
    have hsplit : (fun prf : Digest =>
          Multiset.card ((entry ::ₘ rest).filter (RandomizerGate.PrfClass prf))) =
        fun prf : Digest => (if RandomizerGate.PrfClass prf entry then 1 else 0) +
          Multiset.card (rest.filter (RandomizerGate.PrfClass prf)) := by
      funext prf
      by_cases hentry : RandomizerGate.PrfClass prf entry
      · rw [Multiset.filter_cons_of_pos _ hentry, Multiset.card_cons, if_pos hentry]
        omega
      · rw [Multiset.filter_cons_of_neg _ hentry, if_neg hentry]
        omega
    calc expected ($ᵗ Digest : ProbComp Digest)
          (fun prf => Multiset.card ((entry ::ₘ rest).filter (RandomizerGate.PrfClass prf)))
        = expected ($ᵗ Digest : ProbComp Digest)
            (fun prf => (if RandomizerGate.PrfClass prf entry then 1 else 0) +
              Multiset.card (rest.filter (RandomizerGate.PrfClass prf))) := by
          rw [hsplit]
      _ = expected ($ᵗ Digest : ProbComp Digest)
            (fun prf => if RandomizerGate.PrfClass prf entry then 1 else 0) +
          expected ($ᵗ Digest : ProbComp Digest)
            (fun prf => Multiset.card (rest.filter (RandomizerGate.PrfClass prf))) :=
          expected_add _ _ _
      _ ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((Multiset.card rest : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
          refine add_le_add ?_ ih
          rw [expected_indicator_eq]
          exact prob_prfClass_le entry
      _ = ((Multiset.card (entry ::ₘ rest) : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
          rw [ENNReal.div_add_div_same, Multiset.card_cons]
          push_cast
          ring_nf

end SlhDsaSecurity.PrfClassCount

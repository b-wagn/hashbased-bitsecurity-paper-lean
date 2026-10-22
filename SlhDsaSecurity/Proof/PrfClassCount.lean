import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.ClassExpectation

/-!
# How many of a record's entries are `PRF_msg` inputs at a seed drawn after it

`RandomizerGate.prob_run_randomizerInput_le` charges the **event** that some entry of the record
is a `PRF_msg` input at the drawn seed, at `card / 2 ^ 128`. This file computes the **expected
count** of such entries, which is a different quantity: the obvious route from the event to the
count — bound the count by the record on the event, multiply by the event's probability — gives
`card ^ 2 / 2 ^ 128`, because it bounds the count *before* taking the expectation.

**Summing instead of union-bounding gives the count directly, and it is below one.** Each entry
lies in the class for at most one seed, since `RandomizerGate.prfGuess` recovers the seed from
the input; so each entry contributes at most `2 ^ -128` and the whole count contributes at most
`card / 2 ^ 128`.

**What that turned out to be good for is not what it was proved for.** The count being *small*
is what disqualifies it from carrying the seed clause: the assembly charges each clause at
`expected count / 2 ^ 128` and the union bound gives nothing better than `card record / 2 ^ 128`
for the seed event, so the clause's count has to be record-sized. A clause charged at a
sub-unit count forces its event to be empty. So this file is the measurement of what a sharp
count would have been worth, and `TargetColumn.seedEvent_empty_of_prfClass_charge` is why it
cannot be spent.

**On the general lemmas.** `ClassExpectation.expected_indicator_eq_probEvent` and
`expected_card_filter_le` are the general forms, over a `Finset`, and this file uses the first
rather than restating it. The second does **not** subsume `expected_card_multiset_filter_le`
below: a record is a `Multiset`, so an entry may appear more than once and the `Finset` form
cannot see the multiplicity. The two are siblings rather than a copy and an original.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.PrfClassCount

open Security ClassExpectation

open scoped Classical in
/-- **The `Multiset` sibling of `ClassExpectation.expected_card_filter_le`.** Same statement and
same induction, over a multiset rather than a finite set, because the records this is read at
carry multiplicity. -/
theorem expected_card_multiset_filter_le {β α : Type} (run : ProbComp β)
    (entries : Multiset α) (property : α → β → Prop) (rate : ℝ≥0∞)
    (hrate : ∀ x ∈ entries, Pr[fun value => property x value | run] ≤ rate) :
    expected run (fun value =>
        Multiset.card (entries.filter (fun x => property x value))) ≤
      ((Multiset.card entries : Nat) : ℝ≥0∞) * rate := by
  classical
  induction entries using Multiset.induction_on with
  | empty => simpa using le_of_eq (expected_zero run)
  | cons entry rest ih =>
    have hstep : (fun value : β =>
          Multiset.card ((entry ::ₘ rest).filter (fun x => property x value))) =
        fun value : β => (if property entry value then 1 else 0) +
          Multiset.card (rest.filter (fun x => property x value)) := by
      funext value
      by_cases hprop : property entry value
      · rw [Multiset.filter_cons_of_pos (p := fun x => property x value) rest hprop,
          Multiset.card_cons, if_pos hprop]
        omega
      · rw [Multiset.filter_cons_of_neg (p := fun x => property x value) rest hprop,
          if_neg hprop]
        omega
    rw [hstep, expected_add]
    refine le_trans (add_le_add
      (le_of_eq (expected_indicator_eq_probEvent run (fun value => property entry value)))
      (ih fun x hx => hrate x (Multiset.mem_cons_of_mem hx))) ?_
    refine le_trans (add_le_add (hrate entry (Multiset.mem_cons_self entry rest)) le_rfl) ?_
    rw [Multiset.card_cons]
    push_cast
    ring_nf
    exact le_rfl

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
/-- **And so a record's expected class count is its size over `2 ^ 128`.** The `PRF_msg`
instantiation of the sum above: each entry contributes its own `2 ^ -128` and no more. -/
theorem expected_card_filter_prfClass_le (record : Multiset Bytes) :
    expected ($ᵗ Digest : ProbComp Digest)
        (fun prf => Multiset.card (record.filter (RandomizerGate.PrfClass prf))) ≤
      ((Multiset.card record : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (expected_card_multiset_filter_le ($ᵗ Digest : ProbComp Digest) record
    (fun input prf => RandomizerGate.PrfClass prf input) (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (fun input _ => prob_prfClass_le input)) ?_
  rw [mul_one_div]

end SlhDsaSecurity.PrfClassCount

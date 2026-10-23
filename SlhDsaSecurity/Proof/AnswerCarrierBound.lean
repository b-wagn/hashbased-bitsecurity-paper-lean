import SlhDsaSecurity.Proof.CarrierSplit
import SlhDsaSecurity.Proof.CarrierCap

/-!
# The answer half's bound at the carrier, with the charges discharged

Every piece of the answer half now exists at one run — `SplitTail.splitCarrierTail`, the split
tail — and this file puts them together. The structural charge is
`SplitCarrierTail.prob_bad_splitCarrierTail_le`, the coverage charge is
`SplitTail.prob_splitCarrierTail_targetCovered_le`, the budget is
`SplitTail.splitCarrierTail_share` with `SplitCarrierTail.count_le_of_budget_splitTail`, the
disclosing cap is `CarrierCap.leftRecord_le_cap_of_walk`, and the split is
`CarrierSplit.hsplit_splitCarrierTail`. What is left to supply is the class the counter is split
at and the three facts that name it.

**The class is the message class.** `AnswerCarrier.carrierRightKeep_class` puts the target test
inside it, and `not_isMessageInput_of_canonicalBad` puts the structural clause outside it — the
same separation `AnswerSide.prob_canonicalBad_message_eq_zero` states as a rate, read pathwise,
because the composition needs it per run rather than in expectation.

**What the bound is on.** `hsplit` sends the charged event to *three* clauses: the two charges
and `SplitWitness.SeedRandomised`, the narrowing's leftover. The answer half does not pay for
that one — it is conjoined to the event and charged on the shared side, exactly as the seed
conjunct before it — so the event here carries `¬ SeedRandomised` and the bound is
`q / 2 ^ 128 + 2 ^ -141` with nothing assumed but the walk, the budget, and the two
served-class facts about the recordings.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.AnswerCarrierBound

open Security CanonicalGraph BracketedRun CarrierTail SplitCarrierTail

/-- **The structural clause lives outside the message class**, pathwise.
`AnswerSide.prob_canonicalBad_message_eq_zero` says the same thing as a rate; the composition
needs it per run, and it is the same two lines: on a message input the canonical target is
`none`, so there is nothing for an answer to hit. -/
theorem not_isMessageInput_of_canonicalBad (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (input : Bytes) (answer : HashOutput)
    (hbad : AnswerSide.CanonicalBad publicSeed cells input answer) :
    ¬ CombinedCharge.IsMessageInput pk input := by
  intro hmessage
  rw [AnswerSide.CanonicalBad, CombinedCharge.separated_of_not_possible publicSeed pk cells
    hpublic withinBounds_structural input hmessage] at hbad
  exact absurd hbad (by simp)

end SlhDsaSecurity.AnswerCarrierBound

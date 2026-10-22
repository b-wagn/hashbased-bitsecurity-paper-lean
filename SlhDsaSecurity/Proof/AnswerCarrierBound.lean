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

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The answer half's bound at the carrier's split tail**, with the narrowing's two leftovers
excluded and everything else proved. -/
theorem answerBound_carrier {inside outside : QueryKind} (hne : inside ≠ outside)
    (adversary : Adversary) {q : Nat} (hbudget : Security.HasTotalBudget adversary q)
    (walk : Walk) (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root))
    :
    Pr[fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        (RoutedSplit.AnswerBad ((walk.1, (AnswerShape.forgetRecord z.1).1),
              (AnswerShape.forgetRecord z.1).2.1) ∧
            ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1 (keyAt walk)
              ((AnswerShape.forgetRecord z.1).1, (AnswerShape.forgetRecord z.1).2.1) ∧
            ¬ SplitWitness.LateDisclosure walk.1.1.2.1 (keyAt walk)
              (AnswerShape.forgetRecord z.1)) ∧
          ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk)
            (AnswerShape.forgetRecord z.1).2.1 |
        SplitTail.splitCarrierTail (CombinedCharge.IsMessageInput (keyAt walk)) inside outside
          AnswerCarrier.carrierRightKeep adversary walk] ≤
      ((q : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) + (1 : ENNReal) / 2 ^ 141 := by
  classical
  refine answerBoundExtra_splitTail (CombinedCharge.IsMessageInput (keyAt walk)) hne
    (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
    (fun input => AnswerSide.prob_canonicalBad_le walk.1.1.2.2 walk.1.2 input)
    (fun input answer hbad => not_isMessageInput_of_canonicalBad walk.1.1.2.2 (keyAt walk)
      walk.1.2 hpublic input answer hbad)
    AnswerCarrier.carrierRightKeep adversary walk
    (CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
      (WarmedCharges.walk_cache_canonical hwalk))
    (fun input view hkeep => AnswerCarrier.carrierRightKeep_class walk input view hkeep)
    (5 * 2 ^ 62) q le_rfl ?_ ?_ q ?_
    (fun r => RoutedSplit.AnswerBad ((walk.1, r.1), r.2.1) ∧
      ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1 (keyAt walk) (r.1, r.2.1) ∧
        ¬ SplitWitness.LateDisclosure walk.1.1.2.1 (keyAt walk) r)
    (fun r => SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) r.2.1) ?_
  · exact leftRecord_le_of_carrierTail (CombinedCharge.IsMessageInput (keyAt walk)) hne
      AnswerCarrier.carrierRightKeep adversary walk (5 * 2 ^ 62)
      (CarrierCap.leftRecord_le_cap_of_walk AnswerCarrier.carrierRightKeep hbudget hwalk hpublic)
  · exact fun result hresult => rightRecord_le_of_budget_splitTail
      (CombinedCharge.IsMessageInput (keyAt walk)) hne AnswerCarrier.carrierRightKeep
      hbudget hwalk
      (fun input view hkeep => AnswerCarrier.carrierRightKeep_class walk input view hkeep)
      result hresult
  · exact fun result hresult => count_le_of_budget_splitTail
      (CombinedCharge.IsMessageInput (keyAt walk)) hne AnswerCarrier.carrierRightKeep hbudget
      hwalk result hresult
  · exact CarrierSplit.hsplit_splitCarrierTail (CombinedCharge.IsMessageInput (keyAt walk)) hne
      adversary walk hwalk hgood

end SlhDsaSecurity.AnswerCarrierBound

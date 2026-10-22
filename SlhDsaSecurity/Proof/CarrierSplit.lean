import SlhDsaSecurity.Proof.CarrierJoin
import SlhDsaSecurity.Proof.CarrierCover
import SlhDsaSecurity.Proof.SplitCarrierTail

/-!
# `hsplit`, end to end, and the one seam that does not meet

`AnswerCarrier.hsplit_of_join` takes `hjoin` as a named argument;
`CarrierJoin.targetCovered_carrierTail` is that argument with the cover left open;
`CarrierCover.cover_carrierRightKeep` closes the cover at the carrier's own tests. This file
puts the three together at `AnswerCarrier.answerCarrierRun` and carries the result to
`SplitTail.splitCarrierTail`, where both charges meet.

**One hypothesis survives the assembly, and it is a finding rather than an omission.**

`CarrierCover.cover_carrierRightKeep` holds at the **narrowed** class
`IsMessageInput ∧ ¬ RandomizerGate.PrfClass`, and the narrowing is not cosmetic:
`RandomizerGate.messageInput_eq_randomizerInput_iff` says
`PrfClass prfSeed (messageInput r pk m)` holds exactly when `r = prfSeed`, so the clause the
carrier's `FilesRandomiser` test raises is refuted precisely by knowing the input's randomiser
is not the PRF seed.

`hjoin` supplies `¬ AnswerCoverage.ForgerySeedRandomised`, which says that of the **forgery's**
randomiser alone. The cover is used twice: at the forgery's own digest input, where that is
exactly enough, and at each *disclosing* witness, where it is not — a served request's
randomiser is a value the walk drew, and "it is not the PRF seed" is a guess at a secret, which
at a fixed walk cannot be proved. `AnswerCoverage`'s own header says what to do with such a
residue: conjoin it to the event, visibly, and charge it where the seed is still random.

So the assembly below takes `hseed` at the **cache-wide** leftover,
`SplitWitness.SeedRandomised`, which is what the cache route's join already assumes
(`AnswerCoverage.targetCovered_of_forgeryDisclosedCovered`'s own `hseed`). The gap between the
two is exactly the difference between the forgery-only leftover and the cache-wide one, and it
is where the carrier route and the cache route differ: the carrier's target test carries a
`FilesRandomiser` clause that the cache's does not, and that clause is what reaches back for
the wider hypothesis.

**What this costs, stated plainly.** Either the shared half charges the cache-wide leftover —
which it is already set up to do, the forgery-only version having been introduced as a
*weakening* of it — or the carrier's target test loses its `FilesRandomiser` clause and the
cover is reproved frame-conditionally, with `reaches` threaded and the phase propagation that
`FusedCover` does not have. The first is a ledger question; the second is new machinery.

The other three hypotheses are not findings, only unowned: freshness at the walk's own cache
(the same hypothesis the cache route takes) and the two recording-class facts, which are the
served-agreement and the ordering, and belong to the threads that own those.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierSplit

open Security RecorderView CarriedWitness BracketedRun CarrierTail CoverageRouted

/-- **The narrowed class, from the cache-wide leftover.** -/
theorem narrow_of_not_seedRandomised (walk : Walk) (cache : QueryCache HashSpec)
    (hseed : ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) cache)
    (input : Bytes) (hclass : CombinedCharge.IsMessageInput (keyAt walk) input)
    (hpresent : cache input ≠ none) :
    CombinedCharge.IsMessageInput (keyAt walk) input ∧
      ¬ RandomizerGate.PrfClass walk.1.1.2.1 input :=
  SplitWitness.not_prfClass_of_not_seedRandomised walk.1.1.2.1 (keyAt walk) cache hseed input
    hpresent hclass

set_option maxHeartbeats 1000000 in
/-- **`TargetCovered` at the carrier tail, with the cover discharged.** -/
theorem targetCovered_carrierTail_narrow (adversary : Adversary) (walk : Walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support
      (carrierTail AnswerCarrier.carrierRightKeep adversary walk))
    (hseed : ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) result.2.1)
    (hfreshWalk : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input →
      walk.2 input = none)
    (value : Outcome × Nat)
    (hleftClass : ∀ entry ∈ result.2.2.1,
      ServedLog.servedLog (keyAt walk) (value, result.2.1) entry.1)
    (hrightClass : ∀ entry ∈ result.2.2.2,
      ¬ ServedLog.servedLog (keyAt walk) (value, result.2.1) entry.1)
    (hvalue : value.1 = result.1.1.1)
    (hcovered : ForgeryCoveredBy (ServedLog.servedLog (keyAt walk) (value, result.2.1))
      (keyAt walk) (value, result.2.1)) :
    BlockViews.TargetCovered (σ := QueryCache HashSpec) result :=
  CarrierJoin.targetCovered_carrierTail AnswerCarrier.carrierRightKeep
    (fun input => CombinedCharge.IsMessageInput (keyAt walk) input ∧
      ¬ RandomizerGate.PrfClass walk.1.1.2.1 input)
    (ServedLog.servedLog (keyAt walk) (value, result.2.1)) adversary walk
    (fun probe view hclass _ => CarrierCover.cover_carrierRightKeep walk probe view hclass.1
      hclass.2)
    result hresult (fun input hclass => hfreshWalk input hclass.1) hleftClass hrightClass
    (fun input hclass hpresent =>
      narrow_of_not_seedRandomised walk result.2.1 hseed input hclass hpresent)
    (ServedLog.isMessageInput_of_servedLog (keyAt walk) (value, result.2.1))
    value hvalue hcovered

/-! ## `hjoin` at the answer side's run

`AnswerCarrier.answerCarrierRun` is `AnswerShape.forgetRecord` over the tail, and that map keeps
the whole recorder state, so the coverage event and both recording-class facts read the same
objects on either side of it. `GoodWalk`, `¬ ForgerySeedRandomised` and `¬ LateDisclosure` are
accepted and not used: the first two are subsumed by `hseed` and the third by the recording-class
hypotheses, which is itself worth seeing — it says the carrier route spends the *wider* leftover
and then has no further use for the narrow one. -/

set_option maxHeartbeats 4000000 in
set_option linter.constructorNameAsVariable false in
/-- **A supported result of the answer side's run is one of the tail's**, with the recorder
state and the forgery carried across. The only place this file unfolds `answerCarrierRun`:
`AnswerCarrier`'s own note says everything after `map_answerCarrierRun_eq_tail` must treat the
run as opaque, or the unifier walks into `carrierTail` at every membership, and that is exactly
what it did here before this lemma existed. -/
theorem exists_carrierTail_of_answerCarrierRun (adversary : Adversary) (walk : Walk)
    (result : (Outcome × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support
      (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk)) :
    ∃ rich ∈ support (carrierTail AnswerCarrier.carrierRightKeep adversary walk),
      rich.2 = result.2 ∧ result.1.1 = rich.1.1.1 := by
  rw [AnswerCarrier.answerCarrierRun, support_map] at hresult
  obtain ⟨rich, hrich, hshape⟩ := hresult
  exact ⟨rich, hrich, by rw [← hshape]; rfl, by rw [← hshape]; rfl⟩

attribute [local irreducible] AnswerCarrier.answerCarrierRun

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **`hjoin`, at `answerCarrierRun`.** -/
theorem hjoin_answerCarrierRun (adversary : Adversary) (walk : Walk)
    (hfreshWalk : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input →
      walk.2 input = none)
    (hseed : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) result.2.1)
    (hleftClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.1,
        ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1)
    (hrightClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.2,
        ¬ ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1) :
    ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      Target.GoodWalk walk →
        ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1 (keyAt walk)
            (result.1, result.2.1) →
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1 (keyAt walk) result →
            ForgeryDisclosedCovered (keyAt walk) (result.1, result.2.1) →
              BlockViews.TargetCovered result := by
  intro result hresult _ _ _ hcovered
  have hseedAt := hseed result hresult
  have hleftAt := hleftClass result hresult
  have hrightAt := hrightClass result hresult
  obtain ⟨rich, hrich, hstate, hfst⟩ :=
    exists_carrierTail_of_answerCarrierRun adversary walk result hresult
  have hcov : BlockViews.TargetCovered (σ := QueryCache HashSpec) rich :=
    targetCovered_carrierTail_narrow adversary walk rich hrich (by rw [hstate]; exact hseedAt)
      hfreshWalk result.1 (by rw [hstate]; exact hleftAt) (by rw [hstate]; exact hrightAt) hfst
      (by rw [hstate]; exact hcovered)
  rw [BlockViews.TargetCovered, hstate] at hcov
  exact hcov

/-! ## And `hsplit`, carried to the tail where the charges meet -/

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **`hsplit` at `answerCarrierRun`**, with every piece but the leftover and the two recording
facts discharged. -/
theorem hsplit_answerCarrierRun (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (hfreshWalk : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input →
      walk.2 input = none)
    (hseed : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) result.2.1)
    (hleftClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.1,
        ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1)
    (hrightClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.2,
        ¬ ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1) :
    ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1 (keyAt walk)
            (result.1, result.2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1 (keyAt walk) result →
        GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
            (result.1, result.2.1) ∨
          BlockViews.TargetCovered result :=
  AnswerCarrier.hsplit_of_join AnswerCarrier.carrierRightKeep adversary walk hwalk hgood
    (hjoin_answerCarrierRun adversary walk hfreshWalk hseed hleftClass hrightClass)

set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **And at the split tail**, which is where both charges meet. One `support_map` along
`SplitCarrierTail.map_splitCarrierTail_eq_answerCarrierRun`; no argument changes at either
end. -/
theorem hsplit_splitCarrierTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (adversary : Adversary) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (hfreshWalk : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input →
      walk.2 input = none)
    (hseed : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ¬ SplitWitness.SeedRandomised walk.1.1.2.1 (keyAt walk) result.2.1)
    (hleftClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.1,
        ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1)
    (hrightClass : ∀ result ∈ support
        (AnswerCarrier.answerCarrierRun AnswerCarrier.carrierRightKeep adversary walk),
      ∀ entry ∈ result.2.2.2,
        ¬ ServedLog.servedLog (keyAt walk) (result.1, result.2.1) entry.1) :
    ∀ z ∈ support (SplitTail.splitCarrierTail inClass inside outside
        AnswerCarrier.carrierRightKeep adversary walk),
      RoutedSplit.AnswerBad ((walk.1, (AnswerShape.forgetRecord z.1).1),
            (AnswerShape.forgetRecord z.1).2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1 (keyAt walk)
            ((AnswerShape.forgetRecord z.1).1, (AnswerShape.forgetRecord z.1).2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1 (keyAt walk)
            (AnswerShape.forgetRecord z.1) →
        GrowthCharge.Bad (AnswerSide.CanonicalBad walk.1.1.2.2 walk.1.2)
            ((AnswerShape.forgetRecord z.1).1, (AnswerShape.forgetRecord z.1).2.1) ∨
          BlockViews.TargetCovered (AnswerShape.forgetRecord z.1) := by
  intro z hz
  refine hsplit_answerCarrierRun adversary walk hwalk hgood hfreshWalk hseed hleftClass
    hrightClass (AnswerShape.forgetRecord z.1) ?_
  rw [← SplitCarrierTail.map_splitCarrierTail_eq_answerCarrierRun inClass hne
    AnswerCarrier.carrierRightKeep adversary walk, support_map]
  exact ⟨z, hz, rfl⟩

end SlhDsaSecurity.CarrierSplit

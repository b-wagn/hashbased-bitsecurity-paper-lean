import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.CarrierCoverage

/-!
# The run the answer side owes a bound at, when the tail is the carrier's

`CarrierTail.answerChargedLate_carrier_of_bound` asks for a bound at
`AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk`, and deliberately
leaves that object unnamed, so that the side which has to prove the bound names it once rather
than two shapes drifting apart. This file is that name, and it is the only one.

## It is not `answerRecordedRun`, and there is no map between them

`AnswerJoin.answerRecordedRun` records against `SplitWitness.disclosingKeep`, a test on the
**cache**; the carrier records against `CarriedWitness.disclosingKeep`, which is
`HandlerCarrier.FilesLeft` — a comparison against the **frame in flight**. The two disagree by
construction, and the disagreement *is* the repair: it is what lets the carrier file a served
request whose digest input is already cached, and refuse the signer's own randomiser probe,
neither of which a cache test can do. `AnswerShape.forgetRecord` keeps the whole recorder state,
so the differing records sit inside the mapped value and no map carries one run to the other.

There is a second, independent obstruction: `answerRecordedRun` is one computation under
`RecorderView.recorderOf` from `walk.2`, while the carrier tail is three-stage, bracketed, under
`RecorderView.noticingRecorderOf`, with its count read off the handler. A one-computation run has
no brackets, so no serving, so an empty disclosing record.

## What *does* carry across

Not a map — the interface the charge consumes.
`CoverageCount.prob_bad_or_coverage_le_of_charges` takes the structural clause at its own
expected count, the coverage clause at its own, and the pathwise fact that the two counts share
one budget; it mentions no recorder and no run. Those three propositions at this run are what the
answer side still owes, and the coverage one is the hard half, being the tape factorisation at a
bracketed noticing run.

## And one premise that survives the change of recorder

`RecorderView.noticingRecorderOf` runs `recorderOf` at `CacheView.onQuery state.1 input`, and
`RecorderView.cacheOf_onQuery` says the notice leaves the cache alone. So `appendedOf`'s guard is
still `CacheView.cacheOf state.1 input = none`: the carrier files on a **fresh draw only**,
exactly as the cache recorder does, and `noticingRecorderOf_run_inr_some` shows a cache hit
leaves both recordings untouched. Everything that rests on a filed entry being a fresh uniform
answer — `CoverageCount.rightRecord_length_le_count`, and the per-entry rate the tape
factorisation spends — keeps its premise. What the notice changes is which state the two *tests*
are read at, which is the point of the repair and costs those steps nothing.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.AnswerCarrier

open Security CanonicalGraph WarmedGame Target

/-- The run the answer side owes a bound at, when the tail is the carrier's. -/
noncomputable def answerCarrierRun
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)) :
    ProbComp ((Outcome × Nat) × SplitPrefix.SplitState) :=
  AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk

/-- **It is the run the presentation move asks for**, definitionally, so a bound stated at this
name discharges the obligation through `CarrierTail.answerChargedLate_carrier_of_bound` with no
adapter between them. -/
theorem answerCarrierRun_eq
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)) :
    answerCarrierRun rightKeep adversary walk =
      AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk := rfl

/-- **The obligation at the carrier tail, from a bound stated at the named run.** -/
theorem answerChargedLate_of_carrierBound
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (hbound : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → Security.HasTotalBudget adversary q →
      ∀ walk ∈ support WarmedGame.graphWalk, Target.GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          answerCarrierRun rightKeep adversary walk] ≤
          (q : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
            ((1 : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) +
              (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal))) :
    Obligations.AnswerChargedLate (CarrierTail.carrierTail rightKeep)
      FinalAssembly.forgetFused LateProbes.Ordering :=
  CarrierTail.answerChargedLate_carrier_of_bound rightKeep hbound

/-! ## The target test at the carrier, and the clause that keeps the signer's probe out

`CarrierTail` leaves `rightKeep` a parameter, so the test the target recording is filed under is
chosen here. At the carrier it reads

    narrow input state ∧ ¬ HandlerCarrier.FilesLeft pk state input

and the second conjunct is where the sign has to be watched. `HandlerCarrier.not_filesLeft_randomizerInput`
excludes the signer's own `PRF_msg` probe from the **disclosing** recording — but it is exactly
`¬ FilesLeft` that sends an input to the **target** one, so that lemma says the probe *passes*
the second conjunct. Nothing else keeps it out, and a target-recorded signer query is a query
`SharedJoin.recordOf` does not hold, which is what `LateProvenance.hrecord` needs.

`SplitWitness.narrowClass`'s `¬ PrfClass` clause used to keep it out, by syntax: a `PRF_msg` input
at the real seed is not in the narrowed class whatever the state. That works, and it is the
disguise — it excludes **every** input of that shape rather than the one the signer is making,
and the cases where the two differ are exactly where the FIPS 205 format identity makes a message
input a `PRF_msg` input, which is where the answer half's leftover came from.

`FilesRandomiser` is the honest version: the probe for the frame **in flight**. It is false at
every adversary query, because the flag is down at every boundary; true exactly while the signer
is serving that frame, which is exactly when its probe would be filed; and unforgeable for the
same reason `FilesLeft` is, since only the signing oracle sets the flag. `filesRandomiser_prfClass`
shows it is implied by the syntactic clause, so this is a **weakening** of `narrowClass` and not a
different test — which is the check that was missing the first time a clause was swapped here. -/

/-- **The signer's own randomiser probe, as the flag sees it.** The `PRF_msg` input for the frame
in flight — the exact counterpart of `HandlerCarrier.FilesLeft`, which is the digest input for
that same frame. -/
def FilesRandomiser (prfSeed : Digest) (pk : PublicKey) (state : HandlerCarrier.State)
    (input : Bytes) : Prop :=
  ∃ framed : Bytes, state.framing = some framed ∧
    input = Hashing.randomizerInput prfSeed pk.seed framed

/-- **It is false whenever no request is in flight**, which is every adversary query: the flag is
down at every boundary, so nothing the adversary asks is excluded by this clause. -/
theorem not_filesRandomiser_of_clear (prfSeed : Digest) (pk : PublicKey)
    (state : HandlerCarrier.State) (hclear : state.framing = none) (input : Bytes) :
    ¬ FilesRandomiser prfSeed pk state input := by
  rintro ⟨framed, hframing, -⟩
  rw [hclear] at hframing
  exact absurd hframing (by simp)

/-- **And it is true at the probe itself**, so the signer's own `PRF_msg` query fails the target
test at the state it is made from. This is the clause's whole job. -/
theorem filesRandomiser_probe (prfSeed : Digest) (pk : PublicKey)
    (state : HandlerCarrier.State) (framed : Bytes) (hframing : state.framing = some framed) :
    FilesRandomiser prfSeed pk state (Hashing.randomizerInput prfSeed pk.seed framed) :=
  ⟨framed, hframing, rfl⟩

/-- **The clause is a weakening of the syntactic one**, not a different test: an input the flag
calls the randomiser probe is a `PRF_msg` input at the real seed, so `¬ PrfClass` implies
`¬ FilesRandomiser` and the new target test keeps everything the old one kept, and more. -/
theorem filesRandomiser_prfClass (prfSeed : Digest) (pk : PublicKey)
    (state : HandlerCarrier.State) (input : Bytes)
    (hfiles : FilesRandomiser prfSeed pk state input) :
    RandomizerGate.PrfClass prfSeed input := by
  obtain ⟨framed, -, hinput⟩ := hfiles
  exact ⟨pk.seed, framed, hinput⟩

/-- **The target test at the carrier.** The message class, less the probe for the frame in
flight, less whatever the flag is already filing on the left. -/
def carrierRightKeep
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (input : Bytes) (state : HandlerCarrier.State) : Prop :=
  (CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input ∧
    ¬ FilesRandomiser walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) state input) ∧
  ¬ CarriedWitness.disclosingKeep
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input state

/-- **It keeps the message class**, which is all the budget side reads of it:
`CoverageCount.rightRecord_length_le_count` wants the target test inside the counted class and
nothing more. -/
theorem carrierRightKeep_class
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (input : Bytes) (state : HandlerCarrier.State)
    (hkeep : carrierRightKeep walk input state) :
    CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input :=
  hkeep.1.1

/-- **The signer's own randomiser probe is not target-kept**, at the state it is made from. With
`HandlerCarrier.not_filesLeft_randomizerInput` saying it is not left-kept either, it is filed on
neither side — which is what `LateProvenance.hrecord` needs and what `¬ PrfClass` used to buy by
syntax. -/
theorem not_carrierRightKeep_randomizerInput
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (state : HandlerCarrier.State) (framed : Bytes)
    (hframing : state.framing = some framed) :
    ¬ carrierRightKeep walk
      (Hashing.randomizerInput walk.1.1.2.1
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed framed)
      state :=
  fun hkeep => hkeep.1.2 (filesRandomiser_probe walk.1.1.2.1 _ state framed hframing)

/-! ## The clause buys nothing at the target, and `hsplit` is where that surfaces

**The leftover is not retired here.** It is tempting to read `carrierRightKeep` as having removed
it: the class is the message class with `¬ FilesRandomiser` where `SplitWitness.narrowClass` had
`¬ PrfClass`, and `AnswerCoverage.narrowTarget_messageClass` shows that at the message class
alone `Served.NarrowTarget` is free. The two theorems below say that reading is wrong, in both
directions: at this class `Served.NarrowTarget` is **equivalent** to
`¬ AnswerCoverage.ForgerySeedRandomised`, which is exactly the leftover the cache side pays at
`seedUnits`. Nothing about it is smaller here.

**Why the weakening fails exactly here and nowhere else.** `FilesRandomiser` is `PrfClass` with
its seed and frame witnessed by a *state*, and `filesRandomiser_prfClass` is one half of that.
`Served.NarrowTarget` quantifies over **every** view at which the input is still uncached, so the
other half comes for free: a view with the framing set to the forgery's own frame is a value of
`HandlerCarrier.State` like any other, and it makes the clause fail. Read at one state the
weakening is real — that is `not_carrierRightKeep_randomizerInput`, and it is what the clause was
built for and still does. Read at all states it collapses.

**So `Obligations.SharedChargedLate` at this tail cannot be taken with `seedUnits := 0`**, and
the shape that would make it so is not a smaller charge but a different statement: the target's
demand read at the view its input was *actually answered at*, rather than at every view. That is
the same discipline `SplitWitness.Served` already keeps between its two tests — a filing test is
read at the state a query is made from — and `RecorderView` knows that state. Until such a form
exists, the carrier route owes the same seed charge the cache route does, and
`AnswerCarrier.answerBound_of_charges`' `hsplit` is where the demand will appear. -/

/-- **The leftover defeats the carrier's target test too.** If the forgery's published randomiser
is `SK.prf` then `Served.NarrowTarget` fails at this class, because the demand ranges over every
view at which the input is uncached and one of those has the framing set to the forgery's own
frame. -/
theorem not_narrowTarget_of_forgerySeedRandomised
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (result : (Outcome × Nat) × RecorderView.StateOf HandlerCarrier.State)
    (hforgery : AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
      (result.1, RecorderView.CacheView.cacheOf result.2.1)) :
    ¬ SplitWitness.Served.NarrowTarget
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
      (fun input state => CombinedCharge.IsMessageInput
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input ∧
        ¬ FilesRandomiser walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) state input)
      result := by
  classical
  obtain ⟨message, parsed, hframe, hparsed, seed, framed, hinput⟩ := hforgery
  obtain ⟨-, hseed, -⟩ := Hashing.randomizerInput_injective
    ((FramingLeak.randomizerInput_eq_messageInput parsed.randomizer _ message).trans hinput)
  subst hseed
  intro hnarrow
  have hview := hnarrow message parsed
    (HandlerCarrier.setFraming HandlerCarrier.empty framed) hframe hparsed
    (by
      show HandlerCarrier.cacheOf (HandlerCarrier.setFraming HandlerCarrier.empty framed) _ = none
      simp [HandlerCarrier.cacheOf, HandlerCarrier.empty])
  exact hview.2 ⟨framed, rfl, hinput⟩

/-- **And off the leftover it holds**, by `filesRandomiser_prfClass` at whatever view is offered.
With the theorem above this is an equivalence, which is the whole content: the carrier's class
asks for exactly what the cache's did. -/
theorem narrowTarget_of_not_forgerySeedRandomised
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (result : (Outcome × Nat) × RecorderView.StateOf HandlerCarrier.State)
    (hforgery : ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
      (result.1, RecorderView.CacheView.cacheOf result.2.1)) :
    SplitWitness.Served.NarrowTarget
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
      (fun input state => CombinedCharge.IsMessageInput
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input ∧
        ¬ FilesRandomiser walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) state input)
      result :=
  fun message parsed view hframe hparsed _ =>
    ⟨⟨parsed.randomizer, message, rfl⟩, fun hfiles =>
      hforgery ⟨message, parsed, hframe, hparsed,
        filesRandomiser_prfClass walk.1.1.2.1 _ view _ hfiles⟩⟩

/-! ## And what it is worth once the demand is read where it is used

`SplitWitness.Served.NarrowTargetAt` is the repair: the same demand with the views cut down to
the ones a run can be at. At the carrier the predicate to cut them down by is the **clear
framing**, and it is the right one twice over — it survives a cache update, which is the only
move the recorder makes, and it makes the clause free by `not_filesRandomiser_of_clear`.

What the leftover becomes in exchange is a statement about the run rather than about the
forgery: that the views this recorder is run at have no request in flight. That is not a
probability bound and nothing pays for it.

**It does not follow that the leftover is retired, and an earlier version of this paragraph said
it did.** `reaches` has to be an invariant of the whole run and not a fact about its start,
because `SplitWitness.Served.mem_recordOf_of_cache_reaches` threads it to the view the input is
*answered* at. `CarrierClearFraming.clear_stages` gives the three stage starts and the
adversary's own steps; the opening bracket of a signing sub-run raises the framing on purpose,
so the invariant does not hold inside one. The region where it fails is small and it is not
empty, and `CarrierShared`'s header states what is left of it: a sub-run answers its own digest
input — in which case `FilesLeft` holds and the cover's left disjunct closes it — its own
randomiser input, which by `Hashing.randomizerInput_injective` forces the published randomiser
to be `SK.prf` and the sub-run's frame to be `bytesBE n PK.root ++` the forgery's own, or a
canonical input, which is not a message input off the walk's coincidence.

So on this route the leftover is needed in **one** place rather than at every view, and
`seedUnits := 0` is earned only once that place is closed. `narrowTargetAt_clear` below is free
and is the right shape; what it does not do is discharge the demand inside a sub-run. -/

/-- **The clear framing survives the recorder's one move**, so it is a legitimate `reaches`. -/
theorem clearFraming_cacheAnswer (state : HandlerCarrier.State) (probe : Bytes)
    (answer : HashOutput) (hclear : state.framing = none) :
    (RecorderView.CacheView.update state probe answer).framing = none := by
  show (HandlerCarrier.cacheAnswer state probe answer).framing = none
  rw [HandlerCarrier.framing_cacheAnswer]
  exact hclear

/-- **At views with no request in flight the carrier's target demand is free.** No hypothesis,
no charge, and in particular no `ForgerySeedRandomised`: the clause that
`not_narrowTarget_of_forgerySeedRandomised` refuted at an arbitrary view is vacuous at every
view the recorder is actually run at. -/
theorem narrowTargetAt_clear
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (result : (Outcome × Nat) × RecorderView.StateOf HandlerCarrier.State) :
    SplitWitness.Served.NarrowTargetAt
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
      (fun input state => CombinedCharge.IsMessageInput
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input ∧
        ¬ FilesRandomiser walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) state input)
      (fun state => state.framing = none) result :=
  fun message parsed view _ _ hclear _ =>
    ⟨⟨parsed.randomizer, message, rfl⟩,
      not_filesRandomiser_of_clear walk.1.1.2.1 _ view hclear _⟩

/-! ## The answer half's bound at this run, from three charges and a split

This is the composition side, and it is finished: given the two charges and the fact that their
counts share one budget, the bound follows. What it is **not** is the charges themselves — those
are run-specific, and the coverage one is the tape factorisation at a bracketed noticing run,
which is being proved elsewhere.

The four hypotheses are named so that the two sides meet by `exact` rather than by a second
shape appearing:

* `hsplit` — the charged event implies one of the two clauses. At the cache this is
  `AnswerSide`'s `probEvent_mono` step, where `hdisclosing` moves the coverage clause from the
  signing log to the recorder's own test; at the carrier the two agree by
  `ServingCarrier.AgreesWithLog`, which `CarrierFiles.agreesWithLog_carrierRun` proves.
* `hstructural` — the structural clause at its own expected count.
* `hcoverage` — the coverage clause at its own, with the flat `2 ^ -141` beside it.
* `hshare` — the two counts inside one budget, pathwise.

**None of this can spend concentration margin.** `CoverageCount.prob_bad_or_coverage_le_of_two_charges`
adds two expectations and a constant and contains no tail bound; the margin lives entirely in
whatever proves `hcoverage`. -/

open scoped ENNReal in
/-- **The answer half's bound at the carrier's run.** -/
theorem answerBound_of_charges
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (structuralBad coverageBad : ((Outcome × Nat) × SplitPrefix.SplitState) → Prop)
    (outsideCount insideCount : ((Outcome × Nat) × SplitPrefix.SplitState) → Nat)
    (budget : Nat)
    (hsplit : ∀ result ∈ support (answerCarrierRun rightKeep adversary walk),
      RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result →
        structuralBad result ∨ coverageBad result)
    (hstructural : Pr[structuralBad | answerCarrierRun rightKeep adversary walk] ≤
      ClassExpectation.expected (answerCarrierRun rightKeep adversary walk) outsideCount /
        ((2 ^ 128 : Nat) : ENNReal))
    (hcoverage : Pr[coverageBad | answerCarrierRun rightKeep adversary walk] ≤
      (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal) +
        ClassExpectation.expected (answerCarrierRun rightKeep adversary walk) insideCount /
          ((2 ^ 128 : Nat) : ENNReal))
    (hshare : ∀ result ∈ support (answerCarrierRun rightKeep adversary walk),
      outsideCount result + insideCount result ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
      answerCarrierRun rightKeep adversary walk] ≤
      ((budget : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
        (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal) :=
  le_trans (probEvent_mono hsplit)
    (CoverageCount.prob_bad_or_coverage_le_of_two_charges
      (answerCarrierRun rightKeep adversary walk) structuralBad coverageBad _
      outsideCount insideCount budget hstructural hcoverage hshare)

/-! ## `hcoverage` at this run

`CarrierCoverage.prob_carrierTail_targetCovered_le` charges `BlockViews.TargetCovered` at
`CarrierTail.carrierTail` itself. The event reads the two recordings and nothing else, and
`AnswerShape.forgetRecord` keeps the whole recorder state — it drops the record from the
*value* — so the event is the **same proposition** at either run and the charge transports by
`probEvent_map` with no adapter. The count transports the same way, by `tsum_probOutput_map`.

That is what `AnswerShape.forgetRecord` was chosen for, and it is why the carrier's coverage
charge did not have to be restated here: the one thing that would have broken it is a forgetting
map that drops a recording, and this one does not. -/

open scoped Classical in
/-- **The coverage charge at the run the answer side owes its bound at.** -/
theorem prob_targetCovered_answerCarrierRun_le
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support (CarrierTail.carrierTail rightKeep adversary walk),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (CarrierTail.carrierTail rightKeep adversary walk),
      result.2.2.2.length ≤ rightLength) :
    Pr[BlockViews.TargetCovered | answerCarrierRun rightKeep adversary walk] ≤
      (1 : ENNReal) / 2 ^ 141 +
        ClassExpectation.expected (answerCarrierRun rightKeep adversary walk)
          (fun result => result.2.2.2.length) / ((2 ^ 128 : Nat) : ENNReal) := by
  classical
  have hcount : ClassExpectation.expected (answerCarrierRun rightKeep adversary walk)
      (fun result => result.2.2.2.length) =
      ∑' result, Pr[= result | CarrierTail.carrierTail rightKeep adversary walk] *
        ((result.2.2.2.length : Nat) : ENNReal) := by
    rw [answerCarrierRun, ClassExpectation.expected]
    exact BlockViews.tsum_probOutput_map _ AnswerShape.forgetRecord _
  rw [hcount, answerCarrierRun, probEvent_map]
  exact CarrierCoverage.prob_carrierTail_targetCovered_le rightKeep adversary walk
    leftLength rightLength hcap hleftBound hrightBound

/-! ## The same with the leftover excluded, which is the form this route can actually use

`answerBound_of_charges` above bounds `AnswerBad ∧ ¬ LateDisclosure`, with no seed conjunct. That
is the **strong** form, and taking it is a decision rather than a convenience: its `hsplit` has to
send every supported run with that event to one of the two clauses, including runs where the
forgery's published randomiser is `SK.prf`. On those the narrowing fails —
`not_narrowTarget_of_forgerySeedRandomised`, and `CarrierDemand`'s in-flight branch for the views
`CarrierClearFraming.clear_stages` does not reach — and `hsplit` is a **pathwise** statement, so a
set of small probability does not excuse it. The strong form is not expensive to prove; it is
unavailable.

What the route needs instead is this, and it costs nothing. The event carries
`¬ AnswerCoverage.ForgerySeedRandomised`, so `hsplit` may use it; the event is smaller, so the
same two charges bound it; and the shape is `CarrierTail.answerChargedAt_carrier_of_bound`'s on
the nose, with `budget := q` giving `q / 2 ^ 128 + Target.answerDefectProved` exactly rather than
through a weakening. The leftover then leaves the answer half the way it left the cache half —
conjoined to the event and charged on the shared side at `seedUnits`, where
`CarrierShared.sharedChargedLate_at` already takes it. -/

open scoped ENNReal in
/-- **The answer half's bound at the carrier's run, with the narrowing's leftover excluded.** -/
theorem answerBoundSeed_of_charges
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec))
    (structuralBad coverageBad : ((Outcome × Nat) × SplitPrefix.SplitState) → Prop)
    (outsideCount insideCount : ((Outcome × Nat) × SplitPrefix.SplitState) → Nat)
    (budget : Nat)
    (hsplit : ∀ result ∈ support (answerCarrierRun rightKeep adversary walk),
      RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (result.1, result.2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result →
        structuralBad result ∨ coverageBad result)
    (hstructural : Pr[structuralBad | answerCarrierRun rightKeep adversary walk] ≤
      ClassExpectation.expected (answerCarrierRun rightKeep adversary walk) outsideCount /
        ((2 ^ 128 : Nat) : ENNReal))
    (hcoverage : Pr[coverageBad | answerCarrierRun rightKeep adversary walk] ≤
      (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal) +
        ClassExpectation.expected (answerCarrierRun rightKeep adversary walk) insideCount /
          ((2 ^ 128 : Nat) : ENNReal))
    (hshare : ∀ result ∈ support (answerCarrierRun rightKeep adversary walk),
      outsideCount result + insideCount result ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (result.1, result.2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
      answerCarrierRun rightKeep adversary walk] ≤
      ((budget : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
        (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal) :=
  le_trans (probEvent_mono hsplit)
    (CoverageCount.prob_bad_or_coverage_le_of_two_charges
      (answerCarrierRun rightKeep adversary walk) structuralBad coverageBad _
      outsideCount insideCount budget hstructural hcoverage hshare)

end SlhDsaSecurity.AnswerCarrier

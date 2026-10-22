import SlhDsaSecurity.Proof.RecordColumn
import SlhDsaSecurity.Proof.CarrierDemand

/-!
# The target, with the record charge in the column it belongs to

`ObligationShapes.target_of_answer_and_leaves` and `..._proved` are the assembly `MainTheorem`
and `WholeGameStructural` name, and both spend the narrowing's leftover from **`claims`** —
through `259 + seedUnits ≤ claims`, with `claims + defectUnits ≤ 2 ^ subtreeHeight` capping
`claims` at the slack. That makes `seedUnits` a constant, at most `251` at the live numbers.

`RecordPrfCharge` has since settled that the event it pays for grows with `q`: one recorded
input is one guess at `SK.prf`, because `Hashing.randomizerInput_injective` makes the seed a
function of the input, and the record is the run's own work. A constant against a `q`-shaped
event is not a hypothesis anyone can discharge, so the old tops are not merely unproved — their
`hseed` is false for large `q`, in the same way `InputBullet.bullet_of_bound`'s hypothesis is.

`RecordColumn.sharedChargedLate_of_parts_record_at` is the repair and it is already generic in
the tail, so nothing here reaches into the carrier's files: this is that assembly instantiated
at `FusedCoverage.fusedTail`, with the leftover sent to the record charge by
`SharedAssembly.prob_forgerySeed_le_record` and the ordering term discharged from the fused
tail's own recorder facts rather than assumed.

**What the repair costs, stated rather than hidden.** The `q`-shaped column is not free: it has
to be shown that the record's three parts fit inside one record's worth of budget, which is
`hparts`. That obligation is **owed here, named and unproved**, exactly as it is owed on the
carrier route — the same statement at a different tail. Moving the error into an obligation
somebody can take is the point; the old `hseed` could not be taken by anybody.

The superseded tops stay where they are, with their docstrings saying so, because two files cite
them and a deleted theorem makes a citation dangle.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.TargetColumn

open Security WarmedGame Target RoutedSplit

/-- The ordering term at the fused tail, from that tail's own recorder facts. -/
theorem hordering_fusedTail (adversary : Adversary) :
    Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ LateProbes.Ordering pair |
        LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  LateProbes.prob_ordering_le (FusedCoverage.isRecorderRun adversary)
    (LateProbes.probes_le_recordMessageClass (FusedCoverage.forgetsTo adversary)
      (FusedCoverage.isRecorderRun adversary) (LateProvenance.hrecord adversary))

set_option maxHeartbeats 1000000 in
/-- **The shared half at the fused tail, with the record charge in the `q`-shaped column.**
`hclaims` is `259 ≤ claims`: the constant column pays the input bullet's `259` and nothing else.
-/
theorem sharedChargedLate_fusedTail (claims : Nat) (hclaims : 259 ≤ claims)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            (FinalAssembly.forgetFused pair.2) |
          LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞)) :
    Obligations.SharedChargedLate claims FusedCoverage.fusedTail FinalAssembly.forgetFused
      FinalAssembly.lateOrSeed :=
  RecordColumn.sharedChargedLate_of_parts_record_at FusedCoverage.fusedTail claims
    FinalAssembly.lateOrSeed
    (fun pair => AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
      (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
      (FinalAssembly.forgetFused pair.2))
    hclaims (fun _ hlate => hlate) FusedCoverage.forgetsTo hordering_fusedTail hinput hrecord
    hparts

set_option maxHeartbeats 1000000 in
/-- **The target, at the answer side's proved defect, with the leftover in the right column.**
The replacement for `ObligationShapes.target_of_answer_and_leaves_proved`. -/
theorem target_of_answer_and_leaves_proved (claims : Nat) (hclaims : 259 ≤ claims)
    (hfits : claims + 2 ≤ 2 ^ subtreeHeight)
    (hanswer : Obligations.AnswerChargedAt Target.answerDefectProved FusedCoverage.fusedTail
      FinalAssembly.forgetFused FinalAssembly.lateOrSeed)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            (FinalAssembly.forgetFused pair.2) |
          LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  FinalAssembly.target_of_producers_proved claims hfits hanswer
    (sharedChargedLate_fusedTail claims hclaims hinput hrecord hparts)

set_option maxHeartbeats 1000000 in
/-- **And at the six-unit allowance**, the replacement for
`ObligationShapes.target_of_answer_and_leaves`. -/
theorem target_of_answer_and_leaves (claims : Nat) (hclaims : 259 ≤ claims)
    (hfits : claims + 6 ≤ 2 ^ subtreeHeight)
    (hanswer : Obligations.AnswerChargedLate FusedCoverage.fusedTail FinalAssembly.forgetFused
      FinalAssembly.lateOrSeed)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          AnswerCoverage.ForgerySeedRandomised pair.1.1.1.2.1
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            (FinalAssembly.forgetFused pair.2) |
          LateProbes.pairedOf FusedCoverage.fusedTail adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  FinalAssembly.target_of_producers claims hfits hanswer
    (sharedChargedLate_fusedTail claims hclaims hinput hrecord hparts)

/-! ## What the three parts actually cost, with the overlap in

`RecordColumn` shows the three parts are **not** disjoint and that the overlap is the charged
event itself, so `hparts` at one record's worth is not available. What is available is two
records' worth, and the proof is as short as the claim: the first two parts are disjoint by
construction and the third is a sub-multiset of the record, so each half of the sum is bounded
by the record separately.

That bound is a **ceiling and not a floor**. It says the doubled ledger line suffices; it does
not say the factor is really two, and no adversary attaining it is exhibited here. If the
message-class part can be bounded below the record the factor shrinks and so does the price.
-/

open scoped Classical in
/-- **The three parts fit in two records' worth**, with no hypothesis and no disjointness
between the second and third. -/
theorem card_three_parts_le_two_records (pair : SharedJoin.RecordedPair) :
    Multiset.card (SharedJoin.recordAiming pair) +
        Multiset.card (SharedJoin.recordMessageClass pair) +
      Multiset.card (RecordColumn.recordPrfClass pair) ≤
        2 * Multiset.card (SharedJoin.recordOf pair) := by
  classical
  have hthird : Multiset.card (RecordColumn.recordPrfClass pair) ≤
      Multiset.card (SharedJoin.recordOf pair) :=
    Multiset.card_le_card (Multiset.filter_le _ _)
  have hfirst := SharedJoin.card_parts_le_record pair
  omega

/-! ## And so `hparts` holds, at two records' worth

The pathwise ceiling above is half of it; the other half is `SharedJoin.card_record_le_budget`,
which bounds the record itself by `q - 2 ^ subtreeHeight`. Neither was available until the
second was stated — it was a line inside `card_parts_le_budget`'s proof rather than a lemma —
and with it the composition is the two-part version's, one part longer.

**This is a ceiling and it is proved**, which is the difference between a doubled ledger line
and an arithmetic claim about one. It does not say the factor is two: `RecordColumn` shows the
second and third parts meet, and the counterexample that forbids bounding the message-class part
below the record says nothing about how large the overlap actually is. What it does say is that
no run exceeds two records' worth, so the doubled line is sound whatever the overlap turns out
to be. -/

open scoped Classical in
/-- **`hparts` at two budgets' worth, at any tail that forgets to the game.** The three
expectations add pathwise, the sum is bounded by two records on every run, and the record is
bounded by the budget's slack — so all the tail supplies is that its pairs forget to supported
ones, which is `LateProbes.ForgetsTo`. -/
theorem expected_three_parts_le_two_budgets_at (fused : LateProbes.FusedTail) (q : Nat)
    (adversary : Adversary) (hforget : LateProbes.ForgetsTo fused adversary)
    (hbudget : HasTotalBudget adversary q) :
    ClassExpectation.expected (LateProbes.pairedOf fused adversary)
        (fun pair =>
          Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
      ClassExpectation.expected (LateProbes.pairedOf fused adversary)
        (fun pair =>
          Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
      ClassExpectation.expected (LateProbes.pairedOf fused adversary)
        (fun pair =>
          Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
      ((2 * (q - 2 ^ subtreeHeight) : Nat) : ℝ≥0∞) := by
  classical
  rw [← ClassExpectation.expected_add, ← ClassExpectation.expected_add]
  refine ClassExpectation.expected_le_of_le _ _ _ fun pair hpair => ?_
  have hrecord := SharedJoin.card_record_le_budget adversary q hbudget
    (LateProbes.mem_support_forget hforget hpair)
  have hthree := card_three_parts_le_two_records (LateProbes.forgetRecordings pair)
  omega

open scoped Classical in
/-- **And at the fused tail**, which is where the column reads it. -/
theorem expected_three_parts_le_two_budgets (q : Nat) (adversary : Adversary)
    (hbudget : HasTotalBudget adversary q) :
    ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
        (fun pair =>
          Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
        (fun pair =>
          Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
      ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
        (fun pair =>
          Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
      ((2 * (q - 2 ^ subtreeHeight) : Nat) : ℝ≥0∞) :=
  expected_three_parts_le_two_budgets_at FusedCoverage.fusedTail q adversary
    (FusedCoverage.forgetsTo adversary) hbudget

/-! ## Can one entry carry both charges at once?

The doubling comes from a union bound: the record's message-class part stakes a unit on *"this
entry is a late probe at a fresh draw"* and its `PRF_msg` part stakes one on *"this entry's
randomiser field is the secret"*, and `RecordColumn` shows the two parts meet. A union bound is
an upper bound on our ignorance, so the question is not whether the two events are different —
they are — but whether both units are ever **needed in the same run**.

**They are not, and the reason is that the overlap is the charged event.** An entry in both
parts is a witness for `RandomiserRecord.RecordMeetsPrfClass`, by
`RecordColumn.recordMeetsPrfClass_iff`. So on a run where the seed charge's event **fails**, the
`PRF_msg` part is empty — `recordPrfClass_eq_zero_of_not_recordMeets` — and the three parts fit
in **one** record's worth, which is `card_three_parts_le_record_of_not_recordMeets`. And on a run
where it holds, the shared disjunction is already satisfied by the seed branch, so the ordering
unit at the overlapping entry buys nothing that is not already bought.

**So the two charges partition the runs, not the entries.** The entries do overlap — that is
`RecordColumn.prfClass_messageInput_prf`, and no lemma here contradicts it — but a run pays
either the ordering column or the seed column at those entries, never both. That is what a union
bound over the two parts cannot see, and it is why the `3/2` is slack in the accounting rather
than a loss in the construction.

**What this does not establish.** It does not prove `hparts` at one record's worth
unconditionally — the bound below carries `¬ RecordMeetsPrfClass` as a hypothesis, and turning
that into a charge is a case split in the shared assembly, not a counting lemma. And it is not
an attack result: it says our bound can be sharpened, not that no adversary gains from the
format identity. -/

open scoped Classical in
/-- **Off the seed charge's own event, the `PRF_msg` part of the record is empty.** -/
theorem recordPrfClass_eq_zero_of_not_recordMeets (pair : SharedJoin.RecordedPair)
    (hnot : ¬ RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2) :
    RecordColumn.recordPrfClass pair = 0 := by
  classical
  by_contra hne
  obtain ⟨input, hinput⟩ := Multiset.exists_mem_of_ne_zero hne
  exact hnot ((RecordColumn.recordMeetsPrfClass_iff pair).mpr
    ⟨input, hinput, (Multiset.mem_filter.mp hinput).2⟩)

open scoped Classical in
/-- **And there the three parts fit in one record's worth**, with no subtraction and no
doubling. The doubled line is needed only on runs the seed charge already pays for. -/
theorem card_three_parts_le_record_of_not_recordMeets (pair : SharedJoin.RecordedPair)
    (hnot : ¬ RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2) :
    Multiset.card (SharedJoin.recordAiming pair) +
        Multiset.card (SharedJoin.recordMessageClass pair) +
      Multiset.card (RecordColumn.recordPrfClass pair) ≤
        Multiset.card (SharedJoin.recordOf pair) := by
  classical
  rw [recordPrfClass_eq_zero_of_not_recordMeets pair hnot]
  simpa using SharedJoin.card_parts_le_record pair

/-! ## The count the case split needs, and what is left to state it against

The partition says a run pays the ordering column **or** the seed column, never both. To spend
that, the assembly has to charge the middle disjunct at a count that **vanishes on the runs the
seed branch already pays for**:

    weighedMessageClass pair = if RecordMeetsPrfClass … then 0 else card (recordMessageClass pair)

With that count the three parts fit in **one** record's worth on every good walk, which is
`card_parts_weighed_le_record` below — and that is the inequality `hparts` is asked for, at the
budget the ledger already has. No doubling, no `3 / 2`, no bit lost.

**Both branches are needed and they close differently.** Off the seed event the `PRF_msg` part
is empty and the first two parts are disjoint by construction. On it the middle term is zero and
what is needed is that the *aiming* part and the `PRF_msg` part are disjoint — which they are,
because a `PRF_msg` input aims at no cell (`RedrawCell.locate_randomizerInput`), and that lemma
wants `SK.prf ≠ PK.seed`. That is `Target.GoodWalk`'s **first** conjunct, which the shared side
already carries on every disjunct. So the hypothesis is one the assembly has in hand.

**What is not here.** The ordering charge is still stated at `card (recordMessageClass pair)`,
not at `weighedMessageClass`. Getting the indicator into it is not a weakening of the event —
`LateProbes.prob_ordering_le`'s per-walk step bounds the late-disclosure probability by the
*probes*, and the probes do not vanish on a seed run — so it is a real step and not a transport.
Until it exists this file supplies the counting half and nothing more. -/

open scoped Classical in
/-- The message-class count, charged only on the runs the seed branch does not already pay. -/
noncomputable def weighedMessageClass (pair : SharedJoin.RecordedPair) : Nat :=
  if RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 then 0
  else Multiset.card (SharedJoin.recordMessageClass pair)

open scoped Classical in
/-- **The aiming part and the `PRF_msg` part are disjoint on a good walk**, because a `PRF_msg`
input aims at no cell once the two seeds differ. -/
theorem card_aiming_add_prf_le_record (pair : SharedJoin.RecordedPair)
    (hgood : Target.GoodWalk pair.1) :
    Multiset.card (SharedJoin.recordAiming pair) +
        Multiset.card (RecordColumn.recordPrfClass pair) ≤
      Multiset.card (SharedJoin.recordOf pair) := by
  classical
  have hdisjoint : ∀ input ∈ SharedJoin.recordOf pair,
      ¬ (SharedJoin.AimsSomewhere pair.1.1.1.2.2 input ∧
        RandomizerGate.PrfClass pair.1.1.1.2.1 input) := by
    rintro input - ⟨haims, seed, message, rfl⟩
    exact haims (RedrawCell.locate_randomizerInput pair.1.1.1.2.2 pair.1.1.1.2.1 seed message
      hgood.1)
  rw [SharedJoin.recordAiming, RecordColumn.recordPrfClass, ← Multiset.card_add,
    Multiset.filter_add_filter, Multiset.filter_eq_nil.mpr hdisjoint, add_zero]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

open scoped Classical in
/-- **The three parts fit in one record's worth**, with the middle one weighed. This is the
counting content of the case split: the `3 / 2` was the price of charging both columns on every
run, and no run needs both. -/
theorem card_parts_weighed_le_record (pair : SharedJoin.RecordedPair)
    (hgood : Target.GoodWalk pair.1) :
    Multiset.card (SharedJoin.recordAiming pair) + weighedMessageClass pair +
        Multiset.card (RecordColumn.recordPrfClass pair) ≤
      Multiset.card (SharedJoin.recordOf pair) := by
  classical
  by_cases hmeets : RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2
  · have hzero : weighedMessageClass pair = 0 := by
      rw [weighedMessageClass, if_pos hmeets]
    rw [hzero, add_zero]
    exact card_aiming_add_prf_le_record pair hgood
  · have hweighed : weighedMessageClass pair =
        Multiset.card (SharedJoin.recordMessageClass pair) := by
      rw [weighedMessageClass, if_neg hmeets]
    rw [hweighed, recordPrfClass_eq_zero_of_not_recordMeets pair hmeets]
    simpa using SharedJoin.card_parts_le_record pair

/-! ## The shared half at the weighed count, so the indicator step has somewhere to land

`RecordColumn.sharedChargedLate_of_parts_record_at` charges the ordering column on every run and
therefore needs the three parts to fit twice. This is the same assembly with the middle disjunct
narrowed to `Ordering ∧ ¬ seedEvent` and charged at `weighedMessageClass`, which
`card_parts_weighed_le_record` makes fit **once**.

The narrowing is free at the cover: a run with both `Ordering` and the seed event falls to the
seed disjunct, which is the partition stated as a case split rather than as a count.

`hordering` is the step routed to `LateProbes`' owner and is a hypothesis here. Stating it at
this shape is the point — when that step lands it meets this by `exact`, and if the shapes
differ that is the seam to fix before either side is built on. -/

set_option maxHeartbeats 1000000 in
/-- **The shared obligation with both columns charged where they are owed.** The middle term is
read only on runs the seed branch does not already pay for, so `hparts` is at one record's
worth. -/
theorem sharedChargedLate_weighed_at (fused : LateProbes.FusedTail)
    (claims : Nat) (late seedEvent : LateProbes.SplitPair → Prop)
    (hclaims : 259 ≤ claims)
    (hlate : ∀ pair : LateProbes.SplitPair, late pair →
      LateProbes.Ordering pair ∨ seedEvent pair)
    (hordering : ∀ adversary : Adversary,
      Pr[fun pair : LateProbes.SplitPair =>
          GoodWalk pair.1 ∧ LateProbes.Ordering pair ∧ ¬ seedEvent pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair => weighedMessageClass (LateProbes.forgetRecordings pair)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBulletAt fused adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ seedEvent pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair => weighedMessageClass (LateProbes.forgetRecordings pair)) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair))) ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞)) :
    Obligations.SharedChargedLate claims fused FinalAssembly.forgetFused late := by
  classical
  intro q adversary _ hbudget
  have hordering := hordering adversary
  refine le_trans (probEvent_mono (q := fun pair : LateProbes.SplitPair =>
    (GoodWalk pair.1 ∧ RoutedSplit.InputBad (SharedAssembly.splitTraceOf pair) ∧
        ¬ LateProbes.Ordering pair) ∨
      ((GoodWalk pair.1 ∧ LateProbes.Ordering pair ∧ ¬ seedEvent pair) ∨
        (GoodWalk pair.1 ∧ seedEvent pair))) ?_) ?_
  · rintro pair - ⟨hgood, hshared | hlatePair⟩
    · rcases SharedJoin.cover_of_em
        (fun pair : LateProbes.SplitPair =>
          RoutedSplit.InputBad (SharedAssembly.splitTraceOf pair))
        LateProbes.Ordering pair hshared with hin | hord
      · exact Or.inl ⟨hgood, hin⟩
      · by_cases hseed : seedEvent pair
        · exact Or.inr (Or.inr ⟨hgood, hseed⟩)
        · exact Or.inr (Or.inl ⟨hgood, hord, hseed⟩)
    · rcases hlate pair hlatePair with hord | hseeded
      · by_cases hseed : seedEvent pair
        · exact Or.inr (Or.inr ⟨hgood, hseed⟩)
        · exact Or.inr (Or.inl ⟨hgood, hord, hseed⟩)
      · exact Or.inr (Or.inr ⟨hgood, hseeded⟩)
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget)
    (le_trans (probEvent_or_le _ _ _)
      (add_le_add hordering (hrecord q adversary hbudget)))) ?_
  rw [← add_assoc, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ((259 : Nat) : ℝ≥0∞) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair => weighedMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair)))
      = (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair => weighedMessageClass (LateProbes.forgetRecordings pair)) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (RecordColumn.recordPrfClass (LateProbes.forgetRecordings pair)))) +
          ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((claims : Nat) : ℝ≥0∞) :=
        add_le_add (hparts q adversary hbudget) (Nat.cast_le.mpr hclaims)
    _ = ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The count `hrecord` is stated at, and why no hop can produce it

Building the socket for `hrecord` turned up a defect in `hrecord` itself, so the socket is not
here and this section is what replaces it.

`RecordColumn.sharedChargedLate_of_parts_record_at` asks for

    Pr[GoodWalk ∧ seedEvent] ≤ expected (card (recordPrfClass …)) / 2 ^ 128

and `sharedChargedLate_weighed_at` above inherits it. **That is the wrong count, and no game hop
can supply it**, because the count is zero exactly off the event it is paying for.
`recordPrfClass` filters the record by `PrfClass` *at the walk's own seed*, so by
`recordPrfClass_eq_zero_of_not_recordMeets` it vanishes off the seed event and
`card_prf_le_indicator_record` below bounds it by the whole record on the event. Writing `B` for
a bound on the record's cardinality, that gives

    expected (card recordPrfClass) ≤ B * Pr[GoodWalk ∧ seedEvent]

so the hypothesis would read `Pr ≤ B * Pr / 2 ^ 128`, forcing `Pr = 0` for every adversary with
`B < 2 ^ 128`. The seed event is not impossible — one query at a guessed seed hits with
probability `2 ^ -128` — so the hypothesis is **false**, not unproved.

**What the blind order actually gives** is `RecordPrfCharge.prob_recordMeetsPrfClass_blind`:
`card` guesses from a record of `card` inputs, charged at the **whole** record and bounded by
the run's work. So the honest count is `card (recordOf pair)`, not the `PRF_msg` part of it.

**And that undoes the recovery.** With `hrecord` at the whole record, `hparts` becomes
`aiming + weighed + record ≤ q - 2 ^ subtreeHeight`, and `aiming` is a part of the record, so the
sum reaches two records' worth again. Restricting the seed union bound to the non-aiming entries
does not help: it removes `aiming` from the third term and leaves `record` in it. The `3 / 2` is
back, and `card_three_parts_le_two_records` is again the operative ceiling.

So `sharedChargedLate_weighed_at` and `card_parts_weighed_le_record` are **sound and not
usable**: the weighed count is the right way to spend the ordering column, and the column it was
meant to save is spent elsewhere. They stay, labelled, as the record of an accounting that is
correct about the ordering side and was built on a false hypothesis about the seed side. -/

open scoped Classical in
/-- **The `PRF_msg` part is bounded by the record on the event and by nothing off it.** This is
what makes `hrecord`'s count self-defeating: it is large only where the event it pays for
already holds. -/
theorem card_prf_le_indicator_record (pair : SharedJoin.RecordedPair) :
    Multiset.card (RecordColumn.recordPrfClass pair) ≤
      (if RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 then
        Multiset.card (SharedJoin.recordOf pair) else 0) := by
  classical
  by_cases hmeets : RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2
  · rw [if_pos hmeets]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  · rw [if_neg hmeets, recordPrfClass_eq_zero_of_not_recordMeets pair hmeets]
    simp

/-! ## The shared half at the count the blind charge gives

`hrecord` restated: the seed event is charged against the **whole** record, which is what
`RecordPrfCharge.prob_recordMeetsPrfClass_blind` produces — `card` guesses from `card` inputs —
rather than against the `PRF_msg` part, which cannot pay it.

**The corrected hypothesis does not fit `Obligations.SharedChargedLate`**, and that is the whole
content of this section. Its bound is `(q - 2 ^ subtreeHeight + claims) / 2 ^ 128`, one record's
worth; the three charges now sum to `expected aiming + 259 + expected messageClass +
expected record`, and `aiming` is a part of the record, so the sum reaches **two** records'
worth. So the statement below concludes at the doubled bound with the number written out, rather
than at an obligation whose constant it cannot meet.

That is a lemma with an explicit bound and **not** a ledger line: nothing here restates
`Obligations`, `Target` or any top, and `HasTotalSecurityBits` does not appear. Composing this
to `126` is one arithmetic step — `nat_line_doubled` and `three_q_le_126`, both above — and it is
deliberately not taken here. -/

set_option maxHeartbeats 1000000 in
/-- **The shared side's event, at the doubled line and the honest count.** -/
theorem prob_sharedBad_le_doubled (fused : LateProbes.FusedTail)
    (claims : Nat) (late seedEvent : LateProbes.SplitPair → Prop)
    (hclaims : 259 ≤ claims)
    (hlate : ∀ pair : LateProbes.SplitPair, late pair →
      LateProbes.Ordering pair ∨ seedEvent pair)
    (hordering : ∀ adversary : Adversary,
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ LateProbes.Ordering pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBulletAt fused adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ seedEvent pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordOf (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordOf (LateProbes.forgetRecordings pair))) ≤
        ((2 * (q - 2 ^ subtreeHeight) : Nat) : ℝ≥0∞)) :
    ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧
          (RoutedSplit.InputBad (SharedAssembly.splitTraceOf pair) ∨ late pair) |
        LateProbes.pairedOf fused adversary] ≤
        ((2 * (q - 2 ^ subtreeHeight) + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  intro q adversary _ hbudget
  have hordering := hordering adversary
  refine le_trans (probEvent_mono (q := fun pair : LateProbes.SplitPair =>
    (GoodWalk pair.1 ∧ RoutedSplit.InputBad (SharedAssembly.splitTraceOf pair) ∧
        ¬ LateProbes.Ordering pair) ∨
      ((GoodWalk pair.1 ∧ LateProbes.Ordering pair) ∨
        (GoodWalk pair.1 ∧ seedEvent pair))) ?_) ?_
  · rintro pair - ⟨hgood, hshared | hlatePair⟩
    · exact (SharedJoin.cover_of_em
        (fun pair : LateProbes.SplitPair =>
          RoutedSplit.InputBad (SharedAssembly.splitTraceOf pair))
        LateProbes.Ordering pair hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord =>
          Or.inl ⟨hgood, hord⟩
    · exact Or.inr ((hlate pair hlatePair).imp (fun hord => ⟨hgood, hord⟩)
        fun hseeded => ⟨hgood, hseeded⟩)
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget)
    (le_trans (probEvent_or_le _ _ _)
      (add_le_add hordering (hrecord q adversary hbudget)))) ?_
  rw [← add_assoc, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ((259 : Nat) : ℝ≥0∞) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair)))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordOf (LateProbes.forgetRecordings pair)))
      = (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card
                (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordOf (LateProbes.forgetRecordings pair)))) +
          ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((2 * (q - 2 ^ subtreeHeight) : Nat) : ℝ≥0∞) + ((claims : Nat) : ℝ≥0∞) :=
        add_le_add (hparts q adversary hbudget) (Nat.cast_le.mpr hclaims)
    _ = ((2 * (q - 2 ^ subtreeHeight) + claims : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The refutation, in Lean

`ClassExpectation.expected_indicator_le_probEvent` is what the prose above was missing. With it,
a charge whose count vanishes off the event it pays for is not merely unprovable: it forces the
event to be impossible, for every adversary whose record is shorter than `2 ^ 128`. -/

set_option maxHeartbeats 1000000 in
/-- **A charge against a count that lives only on its own event forces the event empty.** -/
theorem probEvent_eq_zero_of_self_charge {β : Type} (run : ProbComp β) (event : β → Prop)
    [DecidablePred event] (count : β → Nat) (bound : Nat)
    (hbound : ∀ value ∈ support run, event value → count value ≤ bound)
    (hzero : ∀ value, ¬ event value → count value = 0)
    (hsmall : bound < 2 ^ 128)
    (hcharge : Pr[event | run] ≤
      ClassExpectation.expected run count / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | run] = 0 := by
  classical
  by_contra hne
  have hptop : Pr[event | run] ≠ ⊤ := ne_top_of_le_ne_top one_ne_top probEvent_le_one
  have hstep : Pr[event | run] ≤
      (((bound : Nat) : ℝ≥0∞) * Pr[event | run]) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
    hcharge.trans (ENNReal.div_le_div_right
      (ClassExpectation.expected_indicator_le_probEvent run event count bound hbound hzero) _)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)),
    mul_comm (Pr[event | run])] at hstep
  have hdiv := ENNReal.div_le_div_right hstep (Pr[event | run])
  rw [ENNReal.mul_div_cancel_right hne hptop, ENNReal.mul_div_cancel_right hne hptop] at hdiv
  have hnat : (2 ^ 128 : Nat) ≤ bound := by exact_mod_cast hdiv
  omega

/-! ## The third part against the constant column, and the query bound it needs

The budget line, written out: the target is `2 * q / 2 ^ 128`; the answer half spends
`q / 2 ^ 128`; so the shared half has `(q - 2 ^ subtreeHeight + claims) / 2 ^ 128`, of which
`recordAiming` and `recordMessageClass` are disjoint parts of the record and fit in
`q - 2 ^ subtreeHeight` by themselves (`SharedJoin.card_parts_le_record`). **Everything turns on
whether the third part's expectation fits in `claims`** — a constant of at most `510`, not a
`q`-term.

`expected_le_of_self_charge` below is that question answered. The count is zero off the seed
event and at most the record on it, so the bridge gives `expected ≤ B * Pr[seed]`; the seed
charge gives `Pr[seed] ≤ B / 2 ^ 128`; and the two compose to `B ^ 2 / 2 ^ 128`. That is at most
`claims` exactly when `B * B ≤ claims * 2 ^ 128`.

**So the question is not whether `127` closes but up to which `q`**, and the bound belongs in the
statement rather than in a docstring: at `claims = 510` the condition is `B ≤ 22 * 2 ^ 64` and
fails by `2 ^ 69`. `record_fits_claims_at_pow` records the largest power of two that passes.

Two things this does **not** say. It is the blind order throughout — the seed charge it composes
with is `RecordPrfCharge.prob_recordMeetsPrfClass_blind`, and moving it to the real game is the
hop. And `B` here is a cap on the record, which the budget supplies; the answer half's own
tightness, which decides that the shared half really has only `q - 2 ^ subtreeHeight + claims`,
is read off `Obligations` and not re-derived here. -/

set_option maxHeartbeats 1000000 in
/-- **A count that lives on its own charged event is second-order, and fits a constant column
up to an explicit query bound.** -/
theorem expected_le_of_self_charge {β : Type} (run : ProbComp β) (event : β → Prop)
    [DecidablePred event] (count : β → Nat) (bound claims : Nat)
    (hbound : ∀ value ∈ support run, event value → count value ≤ bound)
    (hzero : ∀ value, ¬ event value → count value = 0)
    (hcharge : Pr[event | run] ≤ ((bound : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hthreshold : bound * bound ≤ claims * 2 ^ 128) :
    ClassExpectation.expected run count ≤ ((claims : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (ClassExpectation.expected_indicator_le_probEvent run event count bound
    hbound hzero) ?_
  refine le_trans (mul_le_mul_left' hcharge _) ?_
  rw [← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_of_le_mul ?_
  rw [← Nat.cast_mul]
  refine Nat.cast_le.mpr ?_
  simpa using hthreshold

/-- **The largest power of two the threshold admits at the live constant.** At `claims = 510`
the condition holds at `2 ^ 68` and fails at `2 ^ 69`, so a record of up to `2 ^ 68` entries
keeps the third part inside the constant column. -/
theorem record_fits_claims_at_pow :
    (2 ^ 68 : Nat) * 2 ^ 68 ≤ 510 * 2 ^ 128 ∧ ¬ ((2 ^ 69 : Nat) * 2 ^ 69 ≤ 510 * 2 ^ 128) := by
  constructor
  · norm_num
  · norm_num

/-! ## The same quantity, summed instead of capped, and the threshold goes away

`expected_le_of_self_charge` above caps the count by `B` **on** the event and multiplies by the
event's probability, giving `B ^ 2 / 2 ^ 128` and a query bound. That is the right instrument
when a count is only bounded above. It is the wrong one here, because this count is a **sum of
indicators whose individual probabilities are known**: by `Hashing.randomizerInput_injective`
each recorded input is in `PrfClass prf` for **at most one** `prf`, which is exactly
`RecordPrfCharge.prob_prfClass_single_le`.

So in the blind order linearity gives the quantity directly:

    E[card recordPrfClass] = Σ_{entry ∈ record} Pr[entry ∈ PrfClass prf] ≤ card record / 2 ^ 128

and that is **below one** for every `q < 2 ^ 128`, hence inside any constant column at all. No
threshold, no query bound, and the `claims` column is not even approached.

**The squaring was an artefact of bounding too early** — a sum of small things bounded by one
big thing times one small thing — and it is the same shape as the union bound that could not see
a partition of the runs. `expected_le_of_self_charge` and `record_fits_claims_at_pow` stay as
the record of what that route cost, which is why the exact `2 ^ 68` is worth keeping.

Blind order throughout: `prob_prfClass_single_le` is about a seed drawn after the inputs are
fixed. Moving it to the real game is the hop. -/

open scoped Classical in
/-- **The record's `PRF_msg` part, in the blind order, summed term by term.** -/
theorem expected_card_prfClass_le (inputs : Finset Bytes) :
    ClassExpectation.expected ($ᵗ Digest : ProbComp Digest)
        (fun prfSeed => (inputs.filter fun input =>
          RandomizerGate.PrfClass prfSeed input).card) ≤
      (inputs.card : ℝ≥0∞) * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
  ClassExpectation.expected_card_filter_le ($ᵗ Digest : ProbComp Digest) inputs
    (fun input prfSeed => RandomizerGate.PrfClass prfSeed input)
    (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (fun input _ => RecordPrfCharge.prob_prfClass_single_le input)

open scoped Classical in
/-- **And below one for every record a budgeted run can hold.** A record of at most `bound`
entries with `bound < 2 ^ 128` keeps the part's expectation under a single unit — so it fits the
constant column with the whole column to spare, at every `q` the statement quantifies over. -/
theorem expected_card_prfClass_lt_one (inputs : Finset Bytes) (bound : Nat)
    (hcard : inputs.card ≤ bound) (hsmall : bound < 2 ^ 128) :
    ClassExpectation.expected ($ᵗ Digest : ProbComp Digest)
        (fun prfSeed => (inputs.filter fun input =>
          RandomizerGate.PrfClass prfSeed input).card) ≤ 1 := by
  classical
  refine (expected_card_prfClass_le inputs).trans ?_
  rw [mul_one_div]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  calc ((inputs.card : Nat) : ℝ≥0∞) ≤ ((bound : Nat) : ℝ≥0∞) := Nat.cast_le.mpr hcard
    _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) := Nat.cast_le.mpr (le_of_lt hsmall)

/-! ## Which quantity the assembly needs, settled

The question is whether `hparts` can be fed by `Pr[RecordMeetsPrfClass]` alone or needs the
count. It needs a count, and **not** the `PRF_msg` part's count — that one cannot serve, and the
composition below says so rather than arguing it.

The assembly charges each clause as `Pr[clause] ≤ expected (count) / 2 ^ 128` and then sums the
**counts** against the budget. So the seed clause's count must satisfy
`expected count ≥ 2 ^ 128 * Pr[seed event]`. Since the union bound gives
`Pr[seed event] ≤ card record / 2 ^ 128` and nothing better, the count has to be of the record's
size — and `card (recordPrfClass …)` is not, because `expected_card_prfClass_le` puts it
**below one**. A count below one cannot certify a probability of `card record / 2 ^ 128`.

`seedEvent_empty_of_prfClass_charge` is that stated as a refutation: an assembly taking the seed
clause at the `PRF_msg` part's expectation forces the seed event to be **impossible** for every
adversary whose record is shorter than `2 ^ 128`. So a `claims` column of one unit bought with
that count is bought with a hypothesis nothing satisfies.

**What this does not say.** It does not say the one-unit column is unreachable by some other
route; it says this count cannot buy it. And `expected_card_prfClass_le` is still true and still
useful — the part really is sub-unit — but *being small* is what disqualifies it here, since the
clause it would pay for is not. -/

set_option maxHeartbeats 1000000 in
/-- **An assembly that charges the seed clause at the `PRF_msg` part's expectation forces the
seed event empty.** The count is zero off the event and at most the record on it, so the charge
is self-referential in the sense `probEvent_eq_zero_of_self_charge` rules out. -/
theorem seedEvent_empty_of_prfClass_charge (adversary : Adversary) (bound : Nat)
    (hsmall : bound < 2 ^ 128)
    (hcap : ∀ pair ∈ support (RandomiserRecord.recordedPairedRun adversary),
      Multiset.card (SharedJoin.recordOf pair) ≤ bound)
    (hcharge : Pr[fun pair : SharedJoin.RecordedPair =>
          RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 |
        RandomiserRecord.recordedPairedRun adversary] ≤
      ClassExpectation.expected (RandomiserRecord.recordedPairedRun adversary)
          (fun pair => Multiset.card (RecordColumn.recordPrfClass pair)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : SharedJoin.RecordedPair =>
        RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 |
      RandomiserRecord.recordedPairedRun adversary] = 0 := by
  classical
  refine probEvent_eq_zero_of_self_charge _ _ _ bound ?_ ?_ hsmall hcharge
  · intro pair hpair hevent
    refine le_trans (le_of_eq ?_) (le_trans (card_prf_le_indicator_record pair) ?_)
    · rfl
    · rw [if_pos hevent]
      exact hcap pair hpair
  · intro pair hevent
    rw [recordPrfClass_eq_zero_of_not_recordMeets pair hevent]
    simp

/-! ## Why the seed clause is charged at all, and whether the reduction needs it

Every round so far has taken the clause as given and asked which count pays for it.
`seedEvent_empty_of_prfClass_charge` shows that question has no good answer. The question left
is whether the clause is **necessary** — whether a run on which the adversary has found the seed
still yields the entry the reduction reads.

**It does not, and the reason is structural rather than bookkeeping.** By
`AnswerCarrier.not_narrowTarget_of_forgerySeedRandomised` and `CarrierDemand`'s in-flight
branch, the clause is needed exactly where the forgery's digest input coincides with the
**in-flight frame's own randomiser input** — `case_randomiser`'s conclusion, which forces both
the published randomiser to be `SK.prf` and the served frame to be `bytesBE n PK.root ++` the
forgery's. On such a view that input is kept by **neither** test:
`HandlerCarrier.not_filesLeft_randomizerInput` keeps it out of the disclosing recording and
`AnswerCarrier.not_carrierRightKeep_randomizerInput` out of the target one, which is
`filed_nowhere_at_inflight_randomizer` below.

So the forgery's digest input is in no recording, and the coverage clause — which charges per
entry of the target recording — has nothing to read. The reduction does not merely lose a
convenient hypothesis there; it loses the object it argues about.

**And the exclusion is deliberate on both sides.** Neither test is being conservative: the
signer's randomiser probe is kept out of the disclosing recording because the recorder's test
compares against the frame in flight, and out of the target recording because
`LateProvenance.hrecord` needs every target-recorded input to be a query the record holds, and
the record holds the adversary's and the verifier's queries only. Admitting the probe to either
side breaks a different argument. That is why the clause cannot simply be dropped.

**Conclusion: the reduction genuinely breaks there.** The format identity
`FramingLeak.randomizerInput_eq_messageInput` makes one byte string serve as both a `PRF_msg`
input at the real seed and an `H_msg` input at the forgery's message, and on the runs where the
adversary realises that coincidence the reduction has no recorded entry for the forgery. The
cost is a bit of the theorem, for a structural reason and not a bookkeeping one.

What remains open is the *size* of the event, which is narrower than `ForgerySeedRandomised`:
it needs the signer to have served a request at that one derived frame. Nobody has charged that
narrower event, and it is the only thing left that could change the number. -/

/-- **At a view with a request in flight, the in-flight frame's randomiser input is kept by
neither test.** So if the forgery's digest input coincides with it, the forgery is in no
recording and the coverage clause has no entry to read. -/
theorem filed_nowhere_at_inflight_randomizer
    (walk : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec))
    (state : HandlerCarrier.State) (framed : Bytes)
    (hframing : state.framing = some framed) :
    ¬ CarriedWitness.disclosingKeep
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
        (Hashing.randomizerInput walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed framed)
        state ∧
      ¬ AnswerCarrier.carrierRightKeep walk
        (Hashing.randomizerInput walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed framed)
        state :=
  ⟨HandlerCarrier.not_filesLeft_randomizerInput _ state walk.1.1.2.1 framed hframing,
    AnswerCarrier.not_carrierRightKeep_randomizerInput walk state framed hframing⟩

end SlhDsaSecurity.TargetColumn

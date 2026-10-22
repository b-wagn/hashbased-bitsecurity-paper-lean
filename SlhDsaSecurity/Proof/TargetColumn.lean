import SlhDsaSecurity.Proof.RecordColumn

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

end SlhDsaSecurity.TargetColumn

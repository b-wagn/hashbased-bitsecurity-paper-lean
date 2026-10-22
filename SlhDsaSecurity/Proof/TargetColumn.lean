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

end SlhDsaSecurity.TargetColumn

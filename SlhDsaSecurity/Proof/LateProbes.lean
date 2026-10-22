import SlhDsaSecurity.Proof.LateRate
import SlhDsaSecurity.Proof.SharedJoin

/-!
# The ordering defect, as the shared join reads it

`SharedJoin.hordering_of_probesIn` takes two things from the defect's owner: a charge read at
the owner's own probe count, and a containment putting those probes inside one part of the
record. This file is both, at the recorder's target recording.

**The probe list is the recording's inputs, as a multiset of a list.** `Multiset.card` of
`↑(record.map Prod.fst)` is `record.length`, which is what the charge is stated at. A `toFinset`
would satisfy the containment just as well while lowering the count, and since the charge is
read at the count it would break the charge rather than the containment — the worst place for
it to break, because the join would still typecheck.

**The containment is stated against the part, not against the predicate the part is cut by.**
What the join's message-class part excludes alongside is the join's business and is moving; all
this file needs is that an input in the record and of the right class is in the part, which the
join proves once. So the exclusion can change without anything here changing. That is the
general form and it is worth saying as one: a lemma stated against the object survives the
predicate that defines the object changing, and a lemma stated against the predicate does not.
`probesOf_le` takes the part as a bare `Multiset`, and every use of it below goes through the
join's own membership lemma rather than through either conjunct by name.

What the containment still asks for, and what this file does not prove, is **provenance**: that
a target-recorded input is a query the record holds. The recorder sees every query the run
makes, the record holds the adversary's and the verifier's, and the two coincide here because
nothing else makes a fresh message-class query that the left test does not take first — key
generation queries structural inputs, and the signer's digest query is signer-randomised when
it is made, by its own `PRF_msg` answer, while its `PRF_msg` query is excluded by the narrowing.
Turning that into a proof needs the recorder and the phase record to run on one state, which is
the fusion this file waits on, so it is a hypothesis named `hrecord` and nothing else here
depends on how it is discharged.

**Why the defect is not a predicate of the record, which is why the probes are the recording's
and not the record's.** The record is a multiset: it remembers which queries were made and how
often, not in which order. The defect is an ordering — an entry the right test kept was not
disclosing when it was answered and is disclosing at the end — and the two runs that have to be
told apart differ in nothing else. In the first, the adversary queries
`Hashing.messageInput r pk m` while no `PRF_msg` entry for `m` is in the cache, and the signer's
later answer happens to truncate to `r`; that is the defect, and it costs `2 ^ -128`. In the
second, the signer signs `m` first, the adversary reads `r` off the published signature and
queries the same input; that query is recorded too, since the recording handler records every
query and tests no freshness, and the input is message-class and disclosing at the final cache
just as in the first, with probability one. No predicate of the record and the final cache
separates them — `ServedLog.servedLog` holds in both, the log carrying `m` with published
randomiser `r` either way — so a charge stated on the record alone is either certain or fails to
cover `SplitWitness.LateDisclosure`, which is the hypothesis the answer side is owed.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.LateProbes

open Security SplitPrefix SplitWitness LateRate ClassExpectation

/-! ## The probe list -/

/-- The probes a recording presents: its inputs, as a multiset of the list, so that the count
the charge is stated at survives the conversion. -/
def probesOf (record : List (Bytes × HashOutput)) : Multiset Bytes := ↑(record.map Prod.fst)

@[simp] theorem card_probesOf (record : List (Bytes × HashOutput)) :
    Multiset.card (probesOf record) = record.length := by
  rw [probesOf, Multiset.coe_card, List.length_map]

theorem mem_probesOf {record : List (Bytes × HashOutput)} {input : Bytes}
    (hmem : input ∈ probesOf record) : ∃ entry ∈ record, entry.1 = input := by
  rw [probesOf, Multiset.mem_coe] at hmem
  obtain ⟨entry, hentry, hinput⟩ := List.mem_map.mp hmem
  exact ⟨entry, hentry, hinput⟩

/-! ## The containment, against whatever part the join names -/

/-- **The probes sit inside a part**, given that each recorded input is in it. The recording
holds no input twice, so the containment of multisets is the containment of their elements and
no multiplicity is lost on the way. -/
theorem probesOf_le (part : Multiset Bytes) (record : List (Bytes × HashOutput))
    (hnodup : (record.map Prod.fst).Nodup)
    (hmem : ∀ entry ∈ record, entry.1 ∈ part) : probesOf record ≤ part := by
  classical
  refine (Multiset.le_iff_subset (by rw [probesOf]; exact hnodup)).mpr fun input hinput => ?_
  obtain ⟨entry, hentry, hinput⟩ := mem_probesOf hinput
  rw [← hinput]
  exact hmem entry hentry

/-- **Every target-recorded input is of the message class at the key the tests name.** This is
the half of the containment the recorder settles: the right test keeps the message class, and
what it keeps is what the recording holds. -/
theorem messageClass_of_record (prfSeed : Digest) (pk : PublicKey) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × SplitState)
    (hmem : result ∈ support ((simulateQ (recorder (disclosingKeep prfSeed pk)
      (targetKeep prfSeed pk)) computation).run (cache, [], []))) :
    ∀ entry ∈ result.2.2.2, CombinedCharge.IsMessageInput pk entry.1 :=
  right_record_class (disclosingKeep prfSeed pk) (targetKeep prfSeed pk)
    (CombinedCharge.IsMessageInput pk)
    (fun input inner hkeep => targetKeep_class prfSeed pk input inner hkeep)
    computation (cache, [], []) result hmem (by simp)

/-- **The probes sit inside the join's message-class part.** The key is the walk's, as the part
names it; the class is the recorder's, by `messageClass_of_record`; and `hrecord` is the
provenance step. -/
theorem probesOf_le_recordMessageClass (adversary : Adversary)
    {pair : SharedJoin.RecordedPair}
    (hpair : pair ∈ support (RandomiserRecord.recordedPairedRun adversary))
    (hgood : Target.GoodWalk pair.1) (record : List (Bytes × HashOutput))
    (hnodup : (record.map Prod.fst).Nodup)
    (hclass : ∀ entry ∈ record, CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2) entry.1)
    (hrecord : ∀ entry ∈ record, entry.1 ∈ SharedJoin.recordOf pair) :
    probesOf record ≤ SharedJoin.recordMessageClass pair :=
  probesOf_le _ record hnodup fun entry hentry =>
    SharedJoin.mem_recordMessageClass adversary hpair hgood (hrecord entry hentry)
      (hclass entry hentry)

/-! ## The charge, at the probe count

`prob_lateDisclosure_le` already bounds the defect by the recording's length over `2 ^ 128`.
The join reads that length as the cardinality of the probe list and the rate as a division, and
takes a constant term besides, which here is zero. -/

set_option maxHeartbeats 1000000 in
/-- **The ordering defect, at the probe count the join reads.** -/
theorem prob_lateDisclosure_le_probes (prfSeed : Digest) (pk : PublicKey) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[fun result : α × SplitState => LateDisclosure prfSeed pk result |
        (simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
          computation).run (cache, [], [])] ≤
      (expected ((simulateQ (recorder (disclosingKeep prfSeed pk) (targetKeep prfSeed pk))
            computation).run (cache, [], []))
          (fun result => Multiset.card (probesOf result.2.2.2)) + 0) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [add_zero, show (fun result : α × SplitState => Multiset.card (probesOf result.2.2.2)) =
    (fun result : α × SplitState => result.2.2.2.length) from by
      funext result; exact card_probesOf result.2.2.2]
  refine le_of_le_of_eq (prob_lateDisclosure_le prfSeed pk computation cache) ?_
  rw [rate, mul_one_div]

/-! ## The pair the ordering term is read at

The defect is not a predicate of the recorded pair, for the reason above, so the term is read
at a pair that carries the recordings besides: the walk, a tail result whose **value** holds the
record and whose **state** holds the cache and the two recordings. Everything the join already
has is a predicate of the recorded pair, so it keeps its probability under `forgetRecordings`;
only the ordering term needs the larger object.

What a fused presentation has to supply is two equations about its tail and nothing else: that
it *is* a recorder run at the walk's cache, and that forgetting its recordings returns the
recorded tail. The first is what lets the charge apply, the second what lets the count be read
at the join's own part. Neither mentions the defect. -/

/-- The tail a fused presentation produces: the recorded tail's value, the recorder's state. -/
abbrev FusedTail : Type :=
  Adversary → (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ->
    ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitState)

/-- The pair the ordering term is read at. -/
abbrev SplitPair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    (((Outcome × Multiset Bytes) × Nat) × SplitState)

/-- The paired run at such a tail. -/
noncomputable def pairedOf (fused : FusedTail) (adversary : Adversary) : ProbComp SplitPair := do
  let walk <- WarmedGame.graphWalk
  let result <- fused adversary walk
  pure (walk, result)

/-- The recorded pair a split pair forgets to: the recordings go, the cache stays. -/
def forgetRecordings (pair : SplitPair) : SharedJoin.RecordedPair :=
  (pair.1, (pair.2.1, pair.2.2.1))

/-! ## The averaging, at any tail

`SharedJoin`'s own decompositions are stated at the recorded tail. These are the same three
statements with the tail a parameter, which is all their proofs ever used. -/

theorem probEvent_pairedOf (fused : FusedTail) (adversary : Adversary)
    (event : SplitPair → Prop) :
    Pr[event | pairedOf fused adversary] =
      ∑' walk, Pr[= walk | WarmedGame.graphWalk] *
        Pr[fun result => event (walk, result) | fused adversary walk] := by
  rw [pairedOf, probEvent_bind_eq_tsum]
  refine tsum_congr fun walk => congrArg _ ?_
  rw [bind_pure_comp, probEvent_map]
  rfl

open scoped Classical in
theorem expected_pairedOf (fused : FusedTail) (adversary : Adversary)
    (count : SplitPair → Nat) :
    expected (pairedOf fused adversary) count =
      ∑' walk, Pr[= walk | WarmedGame.graphWalk] *
        expected (fused adversary walk) (fun result => count (walk, result)) := by
  classical
  haveI : DecidableEq SplitPair := Classical.decEq _
  rw [pairedOf, expected_bind]
  refine tsum_congr fun walk => congrArg _ ?_
  rw [bind_pure_comp, expected_map]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A charge proved walk by walk is a charge on the paired run.** -/
theorem prob_le_expected_of_perWalk (fused : FusedTail) (adversary : Adversary)
    (event : SplitPair → Prop) (count : SplitPair → Nat) (extra : ℝ≥0∞)
    (hwalkwise : ∀ walk ∈ support WarmedGame.graphWalk,
      Pr[fun result => event (walk, result) | fused adversary walk] ≤
        (expected (fused adversary walk) (fun result => count (walk, result)) + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | pairedOf fused adversary] ≤
      (expected (pairedOf fused adversary) count + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_pairedOf, expected_pairedOf]
  calc ∑' walk, Pr[= walk | WarmedGame.graphWalk] *
        Pr[fun result => event (walk, result) | fused adversary walk]
      ≤ ∑' walk, Pr[= walk | WarmedGame.graphWalk] *
          ((expected (fused adversary walk) (fun result => count (walk, result)) + extra) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun walk => ?_
        by_cases hmem : walk ∈ support WarmedGame.graphWalk
        · exact mul_le_mul' le_rfl (hwalkwise walk hmem)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = ∑' walk, (Pr[= walk | WarmedGame.graphWalk] *
            expected (fused adversary walk) (fun result => count (walk, result)) +
          Pr[= walk | WarmedGame.graphWalk] * extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine tsum_congr fun walk => ?_
        simp only [div_eq_mul_inv]
        ring
    _ = ((∑' walk, Pr[= walk | WarmedGame.graphWalk] *
            expected (fused adversary walk) (fun result => count (walk, result))) +
          (∑' walk, Pr[= walk | WarmedGame.graphWalk]) * extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ((∑' walk, Pr[= walk | WarmedGame.graphWalk] *
            expected (fused adversary walk) (fun result => count (walk, result))) + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (add_le_add le_rfl ?_) _
        exact le_of_le_of_eq (mul_le_mul' tsum_probOutput_le_one le_rfl) (one_mul extra)

/-! ## What the forgetting map buys

One equation — forgetting the recordings returns the recorded paired run — carries every event
and every count the join already has from the one object to the other, with nothing lost. -/

/-- The equation a fused presentation owes: forgetting the recordings leaves the recorded paired
run.

It is an equality of **distributions**, not of computations. The two are different computations
and will stay different ones, while everything the join reads — a probability, a count, a
support — is a function of the distribution alone. Asking for the stronger equation would be
asking for something nobody can give and nothing here uses. -/
def ForgetsTo (fused : FusedTail) (adversary : Adversary) : Prop :=
  (∀ pair : SharedJoin.RecordedPair,
      Pr[= pair | forgetRecordings <$> pairedOf fused adversary] =
        Pr[= pair | RandomiserRecord.recordedPairedRun adversary]) ∧
    support (forgetRecordings <$> pairedOf fused adversary) ⊆
      support (RandomiserRecord.recordedPairedRun adversary)

open scoped Classical in
/-- **Every event the join already has keeps its probability.** -/
theorem probEvent_forget {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) (event : SharedJoin.RecordedPair → Prop) :
    Pr[fun pair => event (forgetRecordings pair) | pairedOf fused adversary] =
      Pr[event | RandomiserRecord.recordedPairedRun adversary] := by
  classical
  have hmap : Pr[fun pair => event (forgetRecordings pair) | pairedOf fused adversary] =
      Pr[event | forgetRecordings <$> pairedOf fused adversary] :=
    (probEvent_map (pairedOf fused adversary) forgetRecordings event).symm
  rw [hmap, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  exact tsum_congr fun pair => by rw [hforget.1 pair]

open scoped Classical in
/-- **And every count.** -/
theorem expected_forget {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) (count : SharedJoin.RecordedPair → Nat) :
    expected (pairedOf fused adversary) (fun pair => count (forgetRecordings pair)) =
      expected (RandomiserRecord.recordedPairedRun adversary) count := by
  classical
  haveI : DecidableEq SharedJoin.RecordedPair := Classical.decEq _
  have hmap : expected (pairedOf fused adversary) (fun pair => count (forgetRecordings pair)) =
      expected (forgetRecordings <$> pairedOf fused adversary) count :=
    (expected_map (pairedOf fused adversary) forgetRecordings count).symm
  rw [hmap, expected, expected]
  exact tsum_congr fun pair => by rw [hforget.1 pair]

/-- **And every supported pair forgets to a supported one.** -/
theorem mem_support_forget {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) {pair : SplitPair}
    (hpair : pair ∈ support (pairedOf fused adversary)) :
    forgetRecordings pair ∈ support (RandomiserRecord.recordedPairedRun adversary) := by
  refine hforget.2 ?_
  rw [support_map]
  exact ⟨pair, hpair, rfl⟩

/-! ## The ordering term, restated

The event and the probe list are both functions of the split pair. The probes are empty off a
good walk, which is what makes the containment unconditional: the charge is only ever read
against the event, and the event carries `GoodWalk`. -/

/-- The key the tests and the part both name: the walk's. -/
abbrev keyOfPair (pair : SplitPair) : PublicKey :=
  SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2

/-- **The ordering defect at the split pair.** -/
def Ordering (pair : SplitPair) : Prop :=
  LateDisclosure pair.1.1.1.2.1 (keyOfPair pair) pair.2

open scoped Classical in
/-- **The probes the ordering term is charged at**: the target recording's inputs on a good
walk, and nothing off one. -/
noncomputable def probes (pair : SplitPair) : Multiset Bytes :=
  if Target.GoodWalk pair.1 then probesOf pair.2.2.2.2 else 0

theorem card_probes_of_good {pair : SplitPair} (hgood : Target.GoodWalk pair.1) :
    Multiset.card (probes pair) = pair.2.2.2.2.length := by
  classical
  rw [probes, if_pos hgood, card_probesOf]

/-- **The containment, off a good walk**, where the probe list is empty. -/
theorem probes_le_of_not_good {pair : SplitPair} (hgood : ¬ Target.GoodWalk pair.1)
    (part : Multiset Bytes) : probes pair ≤ part := by
  classical
  rw [probes, if_neg hgood]
  exact zero_le

/-- The recorder run a fused tail has to be, at the walk's own cache and the walk's own key. -/
def IsRecorderRun (fused : FusedTail) (adversary : Adversary) : Prop :=
  ∀ walk ∈ support WarmedGame.graphWalk,
    ∃ computation : OracleComp OracleWorld ((Outcome × Multiset Bytes) × Nat),
      fused adversary walk =
        (simulateQ (recorder (disclosingKeep walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
          (targetKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)))
          computation).run (walk.2, [], [])

theorem mem_support_pairedOf {fused : FusedTail} {adversary : Adversary} {pair : SplitPair}
    (hpair : pair ∈ support (pairedOf fused adversary)) :
    ∃ walk ∈ support WarmedGame.graphWalk, ∃ result ∈ support (fused adversary walk),
      (walk, result) = pair := by
  rw [pairedOf, mem_support_bind_iff] at hpair
  obtain ⟨walk, hwalk, hrest⟩ := hpair
  rw [mem_support_bind_iff] at hrest
  obtain ⟨result, hresult, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨walk, hwalk, result, hresult, hpure.symm⟩

open scoped Classical in
/-- **The containment**, with provenance the only thing left to supply. The recording holds each
input once and holds only message-class inputs, and the join's own membership lemma puts a
message-class input of the record in the part. -/
theorem probes_le_recordMessageClass {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) (hshape : IsRecorderRun fused adversary)
    (hrecord : ∀ pair ∈ support (pairedOf fused adversary), Target.GoodWalk pair.1 →
      ∀ entry ∈ pair.2.2.2.2, entry.1 ∈ SharedJoin.recordOf (forgetRecordings pair)) :
    ∀ pair ∈ support (pairedOf fused adversary),
      probes pair ≤ SharedJoin.recordMessageClass (forgetRecordings pair) := by
  classical
  intro pair hpair
  by_cases hgood : Target.GoodWalk pair.1
  · obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := mem_support_pairedOf hpair
    obtain ⟨computation, hcomputation⟩ := hshape walk hwalk
    rw [hcomputation] at hresult
    subst hvalue
    rw [probes, if_pos hgood]
    refine probesOf_le _ _ (right_record_nodup _ _ computation walk.2 result hresult)
      fun entry hentry => ?_
    exact SharedJoin.mem_recordMessageClass adversary (mem_support_forget hforget hpair) hgood
      (hrecord _ hpair hgood entry hentry)
      (messageClass_of_record walk.1.1.2.1
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
        computation walk.2 result hresult entry hentry)
  · exact probes_le_of_not_good hgood _

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering term, at the pair that carries the recordings.** The charge is the one
already proved, read walk by walk; the count is the join's own part, reached by the
containment. -/
theorem prob_ordering_le {fused : FusedTail} {adversary : Adversary}
    (hshape : IsRecorderRun fused adversary)
    (hprobes : ∀ pair ∈ support (pairedOf fused adversary),
      probes pair ≤ SharedJoin.recordMessageClass (forgetRecordings pair)) :
    Pr[fun pair : SplitPair => Target.GoodWalk pair.1 ∧ Ordering pair |
        pairedOf fused adversary] ≤
      expected (pairedOf fused adversary)
          (fun pair => Multiset.card (SharedJoin.recordMessageClass (forgetRecordings pair))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prob_le_expected_of_perWalk fused adversary
    (fun pair => Target.GoodWalk pair.1 ∧ Ordering pair)
    (fun pair => Multiset.card (probes pair)) 0 fun walk hwalk => ?_) ?_
  · by_cases hgood : Target.GoodWalk walk
    · obtain ⟨computation, hcomputation⟩ := hshape walk hwalk
      rw [hcomputation, show (fun result : ((Outcome × Multiset Bytes) × Nat) × SplitState =>
          Multiset.card (probes (walk, result))) =
        (fun result : ((Outcome × Multiset Bytes) × Nat) × SplitState =>
          Multiset.card (probesOf result.2.2.2)) from by
        funext result
        rw [card_probes_of_good (pair := (walk, result)) hgood, card_probesOf]]
      exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
        (prob_lateDisclosure_le_probes walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
          computation walk.2)
    · rw [probEvent_eq_zero fun result _ hbad => hgood hbad.1]
      exact zero_le
  · rw [add_zero]
    exact ENNReal.div_le_div_right (ClassExpectation.expected_mono _ _ _
      fun pair hpair => Multiset.card_le_card (hprobes pair hpair)) _

/-- **The same, with the count read at the join's own run.** -/
theorem prob_ordering_le_recorded {fused : FusedTail} {adversary : Adversary}
    (hforget : ForgetsTo fused adversary) (hshape : IsRecorderRun fused adversary)
    (hprobes : ∀ pair ∈ support (pairedOf fused adversary),
      probes pair ≤ SharedJoin.recordMessageClass (forgetRecordings pair)) :
    Pr[fun pair : SplitPair => Target.GoodWalk pair.1 ∧ Ordering pair |
        pairedOf fused adversary] ≤
      expected (RandomiserRecord.recordedPairedRun adversary)
          (fun pair => Multiset.card (SharedJoin.recordMessageClass pair)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_of_le_of_eq (prob_ordering_le hshape hprobes)
    (congrArg (fun value => value / ((2 ^ 128 : Nat) : ℝ≥0∞))
      (expected_forget hforget (fun pair => Multiset.card (SharedJoin.recordMessageClass pair))))

end SlhDsaSecurity.LateProbes

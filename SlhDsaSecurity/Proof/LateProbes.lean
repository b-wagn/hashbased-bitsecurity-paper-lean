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
join proves once. So the exclusion can change without anything here changing.

What the containment still asks for, and what this file does not prove, is **provenance**: that
a target-recorded input is a query the record holds. The recorder sees every query the run
makes, the record holds the adversary's and the verifier's, and the two coincide here because
nothing else makes a fresh message-class query that the left test does not take first — key
generation queries structural inputs, and the signer's digest query is signer-randomised when
it is made, by its own `PRF_msg` answer, while its `PRF_msg` query is excluded by the narrowing.
Turning that into a proof needs the recorder and the phase record to run on one state, which is
the fusion this file waits on, so it is a hypothesis named `hrecord` and nothing else here
depends on how it is discharged.
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

end SlhDsaSecurity.LateProbes

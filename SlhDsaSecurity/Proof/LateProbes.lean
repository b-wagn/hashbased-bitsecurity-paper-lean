import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.SplitWitness
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Statement.Hashing
import SlhDsaSecurity.Proof.KeygenUniform
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

open Security SplitPrefix SplitWitness

/-! ## The probe list -/

/-! ## The containment, against whatever part the join names -/

/-! ## The charge, at the probe count

`prob_lateDisclosure_le` already bounds the defect by the recording's length over `2 ^ 128`.
The join reads that length as the cardinality of the probe list and the rate as a division, and
takes a constant term besides, which here is zero. -/

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

/-! ## The ordering term, restated

The event and the probe list are both functions of the split pair. The probes are empty off a
good walk, which is what makes the containment unconditional: the charge is only ever read
against the event, and the event carries `GoodWalk`. -/

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

end SlhDsaSecurity.LateProbes

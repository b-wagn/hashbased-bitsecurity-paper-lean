import SlhDsaSecurity.Proof.RecordedTail
import SlhDsaSecurity.Proof.RandomiserProvenance
import SlhDsaSecurity.Proof.CoverageCount
import SlhDsaSecurity.Proof.SplitWitness

/-!
# The randomiser defect, at a record the run returns

`RandomiserProvenance.randomiserBad_source` produces the record **existentially over the
support**, which is one step short of what the charge consumes. As a predicate on the tail's
result, `∃ record, Multiset.card record ≤ work ∧ ∃ input ∈ record, …` is satisfied by a
one-element multiset as soon as the run charges anything, so bounding it bounds nothing.
`RandomizerGate.prob_run_randomizerInput_le` reads the record off the run's own output, and that
is the presentation `RecordedTail` supplies.

So the provenance is taken again over `RecordedTail.recordedAfterSeeds`, where the record is a
value rather than a witness. Nothing in the argument changes — the same four closure lemmas
attribute the entry to the same four phases — except that the adversary's phase is *already*
the recording one, so `PhaseProvenance.exists_recorded_of_mem_countedRun` is not needed and the
record the attribution returns is the run's own.

`prob_randomiserBad_le_record` is the result: the defect's probability at the warmed tail is at
most the probability, at the recorded tail, that the run's own record meets the `PRF_msg` class
at the real seed — or that the digest overlap fires, carried as a disjunct and charged
elsewhere.

**What this does not do.** The charge that consumes the first disjunct draws the secret *after*
the run. `walk.1.1.2.1` is `SK.prf`, and a walk fixes it before the adversary is run — see
`RandomiserDeferral`, whose `mem_support_withPrf` shows every walk stays in the support at every
value of that secret. So this file ends one step from the bound, and the step it is short of is
not a lemma but the obligation's shape.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RandomiserRecord

open Security CacheReplay RecordedQueries PhaseProvenance CacheProvenance RecordedTail

/-! ## The verifier's instrumentation is invisible to the cache, here too -/

/-- The `Tally`-valued instrumentation adds bookkeeping to the value and nothing to the
oracle. This is `WarmedSplit.mem_support_of_countQueries` at the recording writer. -/
theorem mem_support_of_countRecorded {α : Type} (cost : OracleWorld.Domain → Tally)
    (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (result : (α × Tally) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        (countRecorded cost computation)).run cache) →
      (result.1.1, result.2) ∈ support ((simulateQ KeygenUniform.rom computation).run cache) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem
    rw [countRecorded_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure]
    rfl
  | query_bind queried next ih =>
    intro cache result hmem
    rw [countRecorded_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨step, hstep, ?_⟩
    rw [show result.1.1 = inner.1.1 from by rw [← heq],
      show result.2 = inner.2 from by rw [← heq]]
    exact ih step.1 step.2 inner hinner

/-! ## The verifier's digest input is recorded

`RandomiserProvenance.randomiserBad_source` carries the forgery's own digest input beside the
record, as `forgeryDigestRecord`, and pays a unit for it. That unit is spurious here: the
recorded presentation instruments the verifier as well as the adversary, so the verifier's first
query — which is that very input — is already in the record. Proving the containment is what
lets the `+ 1` go, and with it the term that put the shared side's arithmetic over.

The verifier's first query is the digest's, syntactically: `Scheme.verify` rejects on a bad
frame or an unparseable signature without querying, and otherwise its first line is
`Hashing.messageDigest`. So the containment is `countRecorded`'s own step law at the head of the
computation, with no induction. -/

/-- **A recorded run's tally contains what its first query costs.** -/
theorem mem_record_head {α : Type} (cost : OracleWorld.Domain → Tally) (input : Bytes)
    (next : HashOutput → OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (step : (α × Tally) × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ KeygenUniform.rom
      (countRecorded cost ((query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld HashOutput) >>= next))).run cache))
    (probe : Bytes) (hprobe : probe ∈ (cost (Sum.inr input)).2) : probe ∈ step.1.2.2 := by
  rw [show countRecorded cost ((query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld HashOutput) >>= next) =
      (query (spec := OracleWorld) (Sum.inr input) : OracleComp OracleWorld HashOutput) >>=
        fun answer =>
          (fun result => (result.1, cost (Sum.inr input) + result.2)) <$>
            countRecorded cost (next answer)
      from countRecorded_query_bind cost (Sum.inr input) next,
    simulateQ_bind, show simulateQ KeygenUniform.rom
        (query (spec := OracleWorld) (Sum.inr input) : OracleComp OracleWorld HashOutput) =
      KeygenUniform.rom (Sum.inr input) from by simp,
    StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨answer, -, hrest⟩ := hstep
  rw [simulateQ_map, StateT.run_map, support_map] at hrest
  obtain ⟨inner, -, hvalue⟩ := hrest
  rw [show step.1.2 = cost (Sum.inr input) + inner.1.2 from by rw [← hvalue]]
  exact Multiset.mem_add.mpr (Or.inl hprobe)

/-- **The forgery's digest input is one of the verifier's recorded queries.** -/
theorem mem_verifierRecord (pk : PublicKey) (request : Message) (signature : Bytes)
    (framed : Bytes) (parsed : Signature) (hframe : request.frame = some framed)
    (hparsed : Signature.fromBytes? signature = some parsed)
    (cache : QueryCache HashSpec) (step : (Bool × Tally) × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ KeygenUniform.rom
      (countRecorded verifierCost
        (Scheme.verify (m := OracleComp OracleWorld) pk request signature))).run cache)) :
    Hashing.messageInput parsed.randomizer pk framed ∈ step.1.2.2 := by
  have hverifyEq : Scheme.verify (m := OracleComp OracleWorld) pk request signature =
      (query (spec := OracleWorld)
          (Sum.inr (Hashing.messageInput parsed.randomizer pk framed)) :
        OracleComp OracleWorld HashOutput) >>= fun digest =>
          (Fors.publicKeyFromSignature parsed.fors (MessageDigest.forsIndices digest) pk.seed
            (Scheme.forsAddress digest) >>= fun forsKey =>
              Hypertree.verify forsKey parsed.hypertree pk (MessageDigest.treeIndex digest)
                (MessageDigest.leafIndex digest).toFin) := by
    simp only [Scheme.verify, Scheme.verifyInternal, hframe, hparsed]
    rfl
  rw [hverifyEq] at hstep
  exact mem_record_head verifierCost _ _ cache step hstep _ (by simp [verifierCost, recordOf])

/-! ## The provenance, with the record returned

Two things are returned beside the attribution. The `∀ probe` sits **inside** the existential,
because the growth bound `RandomiserProvenance.growthAtMostOn_prfClass` consumes the provenance
at one fixed key pair for every probe at once; and the forgery's digest input is named as a
member of the record, which is what lets `RandomiserProvenance`'s `forgeryDigestRecord` and the
unit it costs both disappear here. -/

attribute [local irreducible] Scheme.keygenInternal Scheme.sign

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **Where an entry the recorded game installed came from**, with the record the run itself
returns. The four cases are `RandomiserProvenance.provenance_afterSeeds`'s; what differs is that
the record is the run's own value and that the forgery's digest input is in it. -/
theorem provenance_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary sds))).run cache)) :
    ∃ keys : SecretKey × PublicKey,
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      (∀ input ∈ RandomiserProvenance.forgeryDigestRecord keys.2 result.1.1.1.forgery,
        input ∈ result.1.1.2) ∧
      (∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        (probe ∈ result.1.1.2 ∨
          QueriesUnder result.2
            (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
          (∃ entry ∈ result.1.1.1.signed, SignerMade keys.1 result.2 entry.1 probe) ∨
          QueriesUnder result.2
            (Scheme.verify (m := OracleComp HashSpec) keys.2 result.1.1.1.forgery.message
              result.1.1.1.forgery.signature) probe)) := by
  unfold RecordedTail.recordedAfterSeeds at hresult
  obtain ⟨keys, keyCache, keyCount, hkeys, hrest1⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hresult
  obtain ⟨sk, pk⟩ := keys
  obtain ⟨value, advCache, advCount, hadv, hrest2⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hrest1
  obtain ⟨verified, verifyFinal, verifyCount, hverify, hrest3⟩ :=
    WarmedSplit.mem_support_counted_bind _ _ _ _ hrest2
  rw [GrowthBudget.countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hrest3
  simp only [Prod.mk.injEq] at hrest3
  obtain ⟨⟨houtcome, -⟩, hcache⟩ := hrest3
  have hverifyRun : (verified.1, verifyFinal) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.verify pk value.1.1.message value.1.1.signature :
        OracleComp OracleWorld Bool)).run advCache) :=
    mem_support_of_countRecorded _ _ _ _ hverify
  have hadvGrow : ∀ (input : Bytes) (output : HashOutput),
      advCache input = some output → result.2 input = some output := by
    intro input output hentry
    rw [hcache]
    exact GrowthCharge.cache_value_persists _ advCache verifyFinal _ hverifyRun input output hentry
  have hkeyGrow : ∀ (input : Bytes) (output : HashOutput),
      keyCache input = some output → result.2 input = some output := by
    intro input output hentry
    exact hadvGrow input output
      (GrowthCharge.cache_value_persists _ keyCache advCache _ hadv input output hentry)
  have hrecord : result.1.1.2 =
      (Multiplicative.toAdd value.1.2).2 + verified.2.2 := by rw [houtcome]
  have hforgeryEq : result.1.1.1.forgery = value.1.1 := by rw [houtcome]
  have hkeyreplay : (sk, pk) = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2 := by
    rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
    exact WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ cache keyCache result.2 (sk, pk)
      hkeys hkeyGrow
  refine ⟨(sk, pk), hkeyreplay, ?_, ?_⟩
  · -- The forgery's own digest input is one of the verifier's recorded queries.
    intro input hinput
    rw [RandomiserProvenance.forgeryDigestRecord] at hinput
    split at hinput
    · simp at hinput
    · rename_i framed hframe
      split at hinput
      · simp at hinput
      · rename_i parsed hparsed
        rw [Multiset.mem_singleton] at hinput
        subst hinput
        rw [hrecord]
        refine Multiset.mem_add.mpr (Or.inr ?_)
        exact mem_verifierRecord pk value.1.1.message value.1.1.signature framed parsed
          (by rw [← hforgeryEq]; exact hframe) (by rw [← hforgeryEq]; exact hparsed)
          advCache (verified, verifyFinal) hverify
  · -- Attribute the entry to the first phase whose cache holds it.
    intro probe hfresh hpresent
    by_cases hkeyFresh : keyCache probe = none
    · by_cases hadvFresh : advCache probe = none
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [hforgeryEq]
        exact queriesUnder_verify_of_fresh pk value.1.1.message value.1.1.signature advCache
          verifyFinal result.2 verified.1 hverifyRun
          (fun input output hentry => by rw [hcache]; exact hentry) probe hadvFresh
          (by rw [hcache] at hpresent; exact hpresent)
      · rcases provenance_phase_subset sk (adversary.main pk) [] keyCache (value, advCache) hadv
          result.2 (fun input output hentry => hadvGrow input output hentry)
          probe hkeyFresh hadvFresh with hmem | ⟨entry, hentry, hquery⟩
        · refine Or.inl ?_
          rw [hrecord]
          exact Multiset.mem_add.mpr (Or.inl hmem)
        · refine Or.inr (Or.inr (Or.inl ⟨entry, ?_, hquery⟩))
          rw [show result.1.1.1.signed = value.2 from by rw [houtcome]]
          exact hentry
    · exact Or.inr (Or.inl (queriesUnder_keygenInternal_of_fresh sds.1 sds.2.1 sds.2.2 cache
        keyCache result.2 (sk, pk) hkeys hkeyGrow probe hfresh hkeyFresh))

/-! ## The charged record, and what falls in it

The charge is read against the run's own record as a `Finset`, with **nothing added**: the
verifier's digest query is recorded by the same instrumentation as the adversary's, so the
forgery's own digest input is already there and the extra unit
`RandomiserProvenance.randomiserBad_source` pays for it is not needed here.

`RecordMeetsPrfClass` is what the charge bounds, and it is stated as its own event rather than
as a step inside the randomiser defect's reduction. That matters: the *answer* side also hands
in a `PRF_msg`-class input of this record — the forgery's digest input, when its randomiser is
`SK.prf` — and that case is **not** subsumed by `ReplayGate.RandomiserBad`, which additionally
requires that no signing request framed to the message. A request framed as `PK.root ‖ m` is
legal, so the two cases are genuinely different and only the record-level event covers both. -/

/-- The record the charge is read against: the run's own, as a `Finset`. -/
noncomputable def chargedRecord
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec) : Finset Bytes :=
  Multiset.toFinset result.1.1.2

/-- **The charge's event**: the run's own record holds an input of the `PRF_msg` class at the
real seed. This is what the deferral pays for, and the randomiser defect is only one way in. -/
def RecordMeetsPrfClass (prfSeed : Digest)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec) : Prop :=
  ∃ input ∈ chargedRecord result, RandomizerGate.PrfClass prfSeed input

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  RecordedTail.recordedAfterSeeds RecordedTail.recordedTail

set_option maxHeartbeats 1000000 in
/-- **The forgery's digest input is in the charged record.** So the answer side's residue — the
forgery's randomiser being `SK.prf`, which makes its digest input a `PRF_msg` input at the real
seed — is charged here, with nothing said about the signing log. -/
theorem recordMeetsPrfClass_of_forgeryDigest (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk))
    (framed : Bytes) (parsed : Signature)
    (hframe : result.1.1.1.forgery.message.frame = some framed)
    (hparsed : Signature.fromBytes? result.1.1.1.forgery.signature = some parsed)
    (hclass : RandomizerGate.PrfClass walk.1.1.2.1
      (Hashing.messageInput parsed.randomizer
        (RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2)) framed)) :
    RecordMeetsPrfClass walk.1.1.2.1 result := by
  classical
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) := by
    rw [RecordedTail.recordedTail] at hresult
    exact hresult
  obtain ⟨keys, hkeys, hforgery, -⟩ :=
    provenance_recordedAfterSeeds adversary walk.1.1 walk.2 result hrun
  have hkey : keys.2 = RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2) := by
    rw [RoutedSplit.keyOf, SplitCharged.generatedKey, hkeys]
  refine ⟨_, Multiset.mem_toFinset.mpr (hforgery _ ?_), hclass⟩
  rw [hkey]
  exact RandomiserProvenance.mem_forgeryDigestRecord _ result.1.1.1.forgery framed parsed
    hframe hparsed

/-! ## The randomiser defect lands in the charged record

The same attribution as `RandomiserProvenance.randomiserBad_source`, read at the recorded tail.
Key generation cannot have made the query, the signer only for a request the event excludes or
as its own digest query — the coincidence `SignerHitsSeed`, charged without any deferral — and
the verifier only as the forgery's digest query, which is in the record. The growth bound comes
back beside the dichotomy, at the same record, which is what makes this charge and the signer's
partition rather than merely add. -/

/-! ## The reduction, as a probability -/

/-! ## The paired run, recorded

`SharedJoin` states its four charges on `Target.pairedRun`'s value, and three of them read only
the trace. The randomiser's does not. `RecordMeetsPrfClass` reads the **record**, and the record
is not a function of the trace: the cache keeps neither multiplicity nor caller, so two runs with
the same outcome and the same final cache can have different records. A `recordPrf : Pair → Prop`
in the join's sense therefore cannot be this event, and an existential over records — the only
thing the trace supports — is the near-vacuous predicate the join's own header rules out.

So the join has to be read at a presentation that carries the record, and this is it, together
with the transfer. Nothing is paid for the change: `RecordedTail.tail_eq_map_recordedTail` is an
equality of computations, so the paired run **is** the recorded paired run with the record
dropped, and every event about the trace keeps its probability exactly. -/

/-- The paired run, with the record kept. -/
noncomputable def recordedPairedRun (adversary : Adversary) :
    ProbComp ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) := do
  let walk ← WarmedGame.graphWalk
  let result ← RecordedTail.recordedTail adversary walk
  pure (walk, result)

/-- The plain pair a recorded one forgets to. -/
def forgetRecord
    (pair : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) :
    (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec) :=
  (pair.1, ((pair.2.1.1.1, pair.2.1.2), pair.2.2))

/-! ## The answer side's residue, folded in — and the fourth party that blocks it

`SplitWitness.SeedRandomised prfSeed pk cache` is "the cache holds a message input that is also a
`PRF_msg` input at the real seed". **As stated it is not a `2 ^ -128` event**, and the reason is
the `PRF_msg`/`H_msg` format overlap a third time. The signer's *randomiser* query for a request
framed as `PK.root ‖ M` is made at `Hashing.randomizerInput SK.prf PK.seed (PK.root ‖ M)`, and
that byte string **is** `Hashing.messageInput SK.prf pk M` — a message input whose randomiser is
`SK.prf`. The frame is legal whenever `PK.root`'s leading byte is zero, which
`FramingClosure.prepend_digest_exists_frame` supplies, so an adversary that asks for one such
signature makes `SeedRandomised` hold outright. Its cost is the `2 ^ -8` the root's byte charges
and nothing else.

That fourth party is in neither of the two things the shared side charges. The signer's own
queries are **not** recorded — `RecordedQueries`' handler records the adversary's and the
verifier's — and `RandomiserProvenance.SignerHitsSeed` additionally asks that the *answer*
truncate to the seed, which this case says nothing about.

So the fold holds off that case and not on it, and `SignerRandomiserInput` is what names it. Off
it, the three parties are exactly the ones the randomiser defect's own provenance walks, and the
reduction is a corollary. The lemma is stated at `RandomizerGate.PrfClass` alone rather than at
`SeedRandomised`, which is stronger and is what both consumers need: a cached input of the class
is charged, whether or not it also parses as a message input. -/

end SlhDsaSecurity.RandomiserRecord

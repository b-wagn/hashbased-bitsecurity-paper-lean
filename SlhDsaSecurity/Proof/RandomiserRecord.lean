import SlhDsaSecurity.Proof.RecordedTail
import SlhDsaSecurity.Proof.RandomiserProvenance

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

/-! ## The provenance, with the record returned -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **Where an entry the recorded game installed came from**, with the record the run itself
returns. The four cases are `RandomiserProvenance.provenance_afterSeeds`'s; only the first
differs, in naming the run's own record rather than one that exists. -/
theorem provenance_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary sds))).run cache))
    (probe : Bytes) (hfresh : cache probe = none) (hpresent : result.2 probe ≠ none) :
    ∃ keys : SecretKey × PublicKey,
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      (probe ∈ result.1.1.2 ∨
        QueriesUnder result.2
          (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
        (∃ entry ∈ result.1.1.1.signed,
          QueriesUnder result.2
            (Scheme.sign (m := OracleComp HashSpec) keys.1 entry.1) probe) ∨
        QueriesUnder result.2
          (Scheme.verify (m := OracleComp HashSpec) keys.2 result.1.1.1.forgery.message
            result.1.1.1.forgery.signature) probe) := by
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
  -- The three phases' caches, and how they grow into the run's own.
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
  have hkeyreplay : (sk, pk) = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2 := by
    rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
    exact WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ cache keyCache result.2 (sk, pk)
      hkeys hkeyGrow
  refine ⟨(sk, pk), hkeyreplay, ?_⟩
  -- Attribute the entry to the first phase whose cache holds it.
  by_cases hkeyFresh : keyCache probe = none
  · by_cases hadvFresh : advCache probe = none
    · -- Only verification is left.
      refine Or.inr (Or.inr (Or.inr ?_))
      rw [show result.1.1.1.forgery = value.1.1 from by rw [houtcome]]
      exact queriesUnder_verify_of_fresh pk value.1.1.message value.1.1.signature advCache
        verifyFinal result.2 verified.1 hverifyRun
        (fun input output hentry => by rw [hcache]; exact hentry) probe hadvFresh
        (by rw [hcache] at hpresent; exact hpresent)
    · -- The adversary's phase installed it, and it is the recording phase.
      rcases provenance_phase_subset sk (adversary.main pk) [] keyCache (value, advCache) hadv
        result.2 (fun input output hentry => hadvGrow input output hentry)
        probe hkeyFresh hadvFresh with hmem | ⟨entry, hentry, hquery⟩
      · refine Or.inl ?_
        rw [hrecord]
        exact Multiset.mem_add.mpr (Or.inl hmem)
      · refine Or.inr (Or.inr (Or.inl ⟨entry, ?_, hquery⟩))
        rw [show result.1.1.1.signed = value.2 from by rw [houtcome]]
        exact hentry
  · -- Key generation installed it.
    exact Or.inr (Or.inl (queriesUnder_keygenInternal_of_fresh sds.1 sds.2.1 sds.2.2 cache
      keyCache result.2 (sk, pk) hkeys hkeyGrow probe hfresh hkeyFresh))

/-! ## The defect, at the run's own record

The same attribution as `RandomiserProvenance.randomiserBad_source`, read at the recorded tail.
Key generation cannot have made the query, the signer only for a request the event excludes or
as its digest query, and the verifier only as the forgery's digest query; the digest cases are
the format overlap and are carried as the second disjunct. What is left is the record, and the
record is now the run's own value. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  RecordedTail.recordedAfterSeeds RecordedTail.recordedTail

set_option maxHeartbeats 1000000 in
/-- **The randomiser defect is an input of the run's own record, or the digest overlap.** -/
theorem randomiserBad_source_record (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk))
    (hbad : ReplayGate.RandomiserBad ((walk.1, (result.1.1.1, result.1.2)), result.2)) :
    (∃ input ∈ result.1.1.2, RandomizerGate.PrfClass walk.1.1.2.1 input) ∨
      ∃ payload framed : Bytes,
        Hashing.randomizerInput walk.1.1.2.1
            (RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2)).seed payload =
          Hashing.messageInput walk.1.1.2.1
            (RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2)) framed := by
  classical
  obtain ⟨message, answer, hentry, hunsigned⟩ := hbad
  set pk := RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2) with hpk
  have hseed : pk.seed = walk.1.1.2.2 := by
    rw [hpk]
    exact (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).1
  have hne : walk.1.1.2.1 ≠ pk.seed := by rw [hseed]; exact hgood.1
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) := by
    rw [RecordedTail.recordedTail] at hresult
    exact hresult
  obtain ⟨keys, hkeys, hsource⟩ :=
    provenance_recordedAfterSeeds adversary walk.1.1 walk.2 result hrun
      (Hashing.randomizerInput walk.1.1.2.1 pk.seed message)
      (RandomiserCharge.walk_cache_prf_fresh hwalk hgood pk.seed message)
      (by rw [hentry]; exact Option.some_ne_none answer)
  have hkey : keys.2 = pk := by rw [hpk, RoutedSplit.keyOf, SplitCharged.generatedKey, hkeys]
  have hsecret : keys.1 = ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ := by
    rw [hkeys, SigningFaithful.keygen_secretKey, hpk, RoutedSplit.keyOf]
  rcases hsource with hmem | hkeygen | ⟨entry, hentryMem, hsign⟩ | hverify
  · exact Or.inl ⟨_, hmem, pk.seed, message, rfl⟩
  · exact absurd hkeygen fun hquery =>
      RandomiserProvenance.keygen_not_randomizerInput result.2 walk.1.1.1 walk.1.1.2.1
        walk.1.1.2.2 walk.1.1.2.1 pk.seed message hgood.1 hquery
  · rw [hsecret] at hsign
    obtain ⟨framed, hframe, hmessage⟩ :=
      RandomiserProvenance.sign_messageProbe result.2 ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ entry.1
        walk.1.1.2.1 pk.seed message hne hsign
    rcases hmessage with hrandomizer | hdigest
    · obtain ⟨-, -, hequal⟩ := Hashing.randomizerInput_injective hrandomizer
      exact absurd ⟨entry, hentryMem, hequal ▸ hframe⟩ hunsigned
    · refine Or.inr ⟨message, framed, ?_⟩
      rw [hdigest, RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 pk.seed pk
        framed message hdigest.symm]
  · obtain ⟨framed, parsed, -, -, hdigest⟩ :=
      VerifierFormat.verify_probe_randomizerInput result.2 keys.2
        result.1.1.1.forgery.message result.1.1.1.forgery.signature walk.1.1.2.1 pk.seed message
        (by rw [hkey]; exact hne) hverify rfl
    rw [hkey] at hdigest
    refine Or.inr ⟨message, framed, ?_⟩
    rw [hdigest, RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 pk.seed pk
      framed message hdigest.symm]

/-! ## The reduction, as a probability

With the attribution pointwise on the support, the defect's probability at the warmed tail is a
probability at the recorded tail about two named things: the run's own record meeting the
`PRF_msg` class at the real seed, and the digest overlap. The record is written as a `Finset`
here because that is what `RandomiserDeferral.prob_record_meets_prfClass_le` — and
`RandomizerGate.prob_run_randomizerInput_le` behind it — consumes, and
`RecordedTail.card_toFinset_le_count` caps its size by the run's own charged work. -/

/-- The digest overlap, as an event about a recorded result: the forgery's or a request's
digest query is a `PRF_msg` input at `SK.prf` itself. Charged elsewhere. -/
def DigestOverlap (prf : Digest)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)
    (walkValue : (Digest × Digest × Digest) × CanonicalGraph.Cells) : Prop :=
  ∃ payload framed : Bytes,
    Hashing.randomizerInput prf
        (RoutedSplit.keyOf ((walkValue, (result.1.1.1, result.1.2)), result.2)).seed payload =
      Hashing.messageInput prf
        (RoutedSplit.keyOf ((walkValue, (result.1.1.1, result.1.2)), result.2)) framed

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- **The randomiser defect, reduced to the record and the overlap.** -/
theorem prob_randomiserBad_le_record (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr[fun result => ReplayGate.RandomiserBad ((walk.1, result.1), result.2) |
        WarmedGame.tail adversary walk] ≤
      Pr[fun result =>
          (∃ input ∈ Multiset.toFinset result.1.1.2,
            RandomizerGate.PrfClass walk.1.1.2.1 input) ∨
          DigestOverlap walk.1.1.2.1 result walk.1 |
        RecordedTail.recordedTail adversary walk] := by
  classical
  rw [RecordedTail.probEvent_tail_eq]
  refine probEvent_mono fun result hresult hbad => ?_
  rcases randomiserBad_source_record adversary hwalk hgood hresult hbad with
    ⟨input, hinput, hclass⟩ | hoverlap
  · exact Or.inl ⟨input, Multiset.mem_toFinset.mpr hinput, hclass⟩
  · exact Or.inr hoverlap

end SlhDsaSecurity.RandomiserRecord

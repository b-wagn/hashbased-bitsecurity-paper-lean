import SlhDsaSecurity.Proof.FusedCoverage
import SlhDsaSecurity.Proof.RandomiserProvenance

/-!
# Who made a target-recorded query

The ordering term's containment asks one thing the recorder cannot answer by itself: that an
input the target recording holds is a query the **record** holds. The recorder sees every query
the run makes, the record only the adversary's and the verifier's, and the two coincide here
because of what the other parties ask.

Key generation asks at canonical inputs, which are not message inputs once the key is no
coincidence. The signer asks at canonical inputs, at its request's own `PRF_msg` input — which
the narrowing excludes — and at its request's own digest input, which is signer-randomised at
the moment it is made, by the answer the signer has just drawn, and so is taken by the left test
rather than the right. Nothing else is left, and the adversary's and the verifier's queries are
recorded by construction.

The provenance itself is `RandomiserProvenance.provenance_afterSeeds`'s argument at the recorded
game: the run is split at its three sequencing points and the entry attributed to the first
phase whose cache holds it. What differs is the record. There the record is produced by an
existence proof beside the run; here it is the one the run's own value carries, which is the one
`SharedJoin.recordOf` reads and the one `RecordedTail.card_eq_work` counts — so the containment
lands in the part the join names rather than in a multiset that merely has the same size.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.LateProvenance

open Security CacheReplay RecordedQueries CacheProvenance PhaseProvenance

/-! ## The verifier records what it asks -/

/-- **A fresh query the verifier's phase installed is in the record it keeps.** The phase charges
and records at the same step, so an entry that was not there before is one of the inputs it
wrote down. -/
theorem mem_record_countRecorded {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (result : (α × Tally) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom
        (countRecorded verifierCost computation)).run cache) →
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        probe ∈ result.1.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache result hmem probe hfresh hpresent
    rw [countRecorded_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [show result.2 = cache from by rw [hmem]] at hpresent
    exact absurd hfresh hpresent
  | query_bind queried next ih =>
    intro cache result hmem probe hfresh hpresent
    rw [countRecorded_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hcache : result.2 = inner.2 := by rw [← heq]
    have hrecord : result.1.2 = verifierCost queried + inner.1.2 := by rw [← heq]
    rw [hrecord]
    show probe ∈ (verifierCost queried).2 + inner.1.2.2
    by_cases hstepfresh : step.2 probe = none
    · exact Multiset.mem_add.mpr (Or.inr
        (ih step.1 step.2 inner hinner probe hstepfresh (by rw [← hcache]; exact hpresent)))
    · refine Multiset.mem_add.mpr (Or.inl ?_)
      rw [show (verifierCost queried).2 = recordOf queried from rfl,
        show queried = Sum.inr probe from
          queried_of_fresh_step queried cache step (by simpa using hstep) probe hfresh hstepfresh]
      simp [recordOf]

/-! ## Two readings of a generated key

Key generation's last line builds the pair, so its secret key carries the seed it was given and
the public key beside it. Both are definitional, and both are stated before the phase splits
make `Scheme.keygenInternal` opaque. -/

theorem keygen_prf (cache : QueryCache HashSpec) (secretSeed prfSeed publicSeed : Digest) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
      secretSeed prfSeed publicSeed).1.prf = prfSeed := rfl

theorem keygen_publicKey (cache : QueryCache HashSpec) (secretSeed prfSeed publicSeed : Digest) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1.publicKey =
      (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).2 := rfl

/-! ## Where an entry the recorded game installed came from

The run is split at its three sequencing points and the entry attributed to the first phase
whose cache holds it. The verifier's phase is not a case: it records what it asks, so an entry
it installed is already in the record the run's value carries. -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **An entry the recorded game installed is the adversary's or the verifier's own query, key
generation's, or a signing sub-run's.** The record is the one the run's own value carries. -/
theorem provenance_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec)
    (result : (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec))
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary sds))).run cache)) :
    ∃ keys : SecretKey × PublicKey,
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
        probe ∈ result.1.1.2 ∨
          QueriesUnder result.2
            (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
          ∃ entry ∈ result.1.1.1.signed, SignerMade keys.1 result.2 entry.1 probe := by
  rw [RecordedTail.recordedAfterSeeds] at hresult
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
  have hadvGrow : ∀ (input : Bytes) (output : HashOutput),
      advCache input = some output → result.2 input = some output := by
    intro input output hentry
    rw [hcache]
    exact GrowthCharge.cache_value_persists _ advCache verifyFinal _ hverify input output hentry
  have hkeyGrow : ∀ (input : Bytes) (output : HashOutput),
      keyCache input = some output → result.2 input = some output := by
    intro input output hentry
    exact hadvGrow input output
      (GrowthCharge.cache_value_persists _ keyCache advCache _ hadv input output hentry)
  have hkeyreplay : (sk, pk) = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2 := by
    rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
    exact WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ cache keyCache result.2 (sk, pk)
      hkeys hkeyGrow
  refine ⟨(sk, pk), hkeyreplay, ?_⟩
  intro probe hfresh hpresent
  by_cases hkeyFresh : keyCache probe = none
  · by_cases hadvFresh : advCache probe = none
    · refine Or.inl ?_
      rw [show result.1.1.2 = (Multiplicative.toAdd value.1.2).2 + verified.2.2 from by
        rw [houtcome]]
      exact Multiset.mem_add.mpr (Or.inr
        (mem_record_countRecorded _ advCache (verified, verifyFinal) hverify probe hadvFresh
          (by rw [hcache] at hpresent; exact hpresent)))
    · rcases provenance_phase_subset sk (adversary.main pk) [] keyCache (value, advCache) hadv
        result.2 (fun input output hentry => hadvGrow input output hentry)
        probe hkeyFresh hadvFresh with hmem | ⟨entry, hentry, hquery⟩
      · refine Or.inl ?_
        rw [show result.1.1.2 = (Multiplicative.toAdd value.1.2).2 + verified.2.2 from by
          rw [houtcome]]
        exact Multiset.mem_add.mpr (Or.inl hmem)
      · refine Or.inr (Or.inr ⟨entry, ?_, hquery⟩)
        rw [show result.1.1.1.signed = value.2 from by rw [houtcome]]
        exact hentry
  · exact Or.inr (Or.inl (queriesUnder_keygenInternal_of_fresh sds.1 sds.2.1 sds.2.2 cache
      keyCache result.2 (sk, pk) hkeys hkeyGrow probe hfresh hkeyFresh))

/-! ## The containment, with one branch named

Three of provenance's four parties are settled here. The adversary's and the verifier's queries
are the record. Key generation's are canonical, and a canonical input is not a message input
once the key is no coincidence. The signer asks at canonical inputs, at its request's own
`PRF_msg` input — which the narrowing excludes — and at its request's own digest input.

That last one is the branch left standing, and it is left standing for a reason worth stating
exactly, because getting it wrong is what made the first version of the hypothesis false.

**Replay is faithful to a run only at the run's final cache.** That is the invariant inside
`CacheReplay.cached_of_queriesUnder` — each query's answer is in the final cache, so replaying
there reproduces the continuations the run took — and it is why provenance is stated at
`result.2`. At any *intermediate* cache the replay diverges, since a miss replays to `default`.
That divergence is not an aside: it is the whole of the counterexample in
`ObligationShapes`, where the replayed randomiser of a message that was never signed is the
fixed constant `truncate default`, which an adversary can compute and query.

So the three settled cases are settled because they read the **input alone** — "not
message-class" and "in the `PRF_msg` class at the real seed" are predicates on bytes, and a
replay-at-the-final-cache statement settles them with the cache never entering. The digest case
is the one that reads the **state**, and it has to be read at the step the query was made at.
`SignerDigestStep.signerRandomised_digest` is that fact about the run, and it costs two
unfoldings rather than an induction, because `Scheme.signInternal`'s randomiser and digest
queries are adjacent and the second's input is built from the first's answer.

What is still missing is the bridge between them: provenance names the party that installed an
entry, `SplitPrefix.right_record_witness` names the cache the recorder filed it at, and nothing
yet says these are the same step. They are — an input is installed exactly once, and both
lemmas speak of that occasion — but neither hands back an object the other can be matched
against. That is the same discipline `ProbeContainment.claimsOf_carrier` keeps on the input
half: entries and the state they are read at, instantiated at one object. -/

/-- The secret key the walk's seeds generate, read from the run's own cache. -/
noncomputable def secretKeyOf (pair : LateProbes.SplitPair) : SecretKey :=
  (@Scheme.keygenInternal Id Id.instMonad (replayQuery pair.2.2.1)
    pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2).1

/-- **The branch provenance leaves**: no target-recorded input is a served request's own digest
input.

**The guard is not decoration, and its absence made the earlier version false.**
`HonestProbes.replayRandomizer` reads the randomiser off the final cache through
`CacheReplay.replay`, which answers a miss with `default`. Without the guard the statement
therefore says something about `messageInput (truncate default) pk m` for every `m`, including
messages never signed — a byte string the adversary can compute and query, and
`ObligationShapes.targetKeep_default` shows the target test takes it. A one-query adversary
refuted it. The guard says the final cache really does hold the request's `PRF_msg` answer, so
the replayed randomiser is the signer's own and not a fabricated constant; it is supplied where
this is used, from `PhaseProvenance.SignerMade`'s second conjunct, which carries exactly that
from where the sub-run was in hand.

What remains is true for the reason the old docstring gave — such a query is signer-randomised
when it is made, so the left test takes it — and what is still missing to prove it is named in
the section note above: the cache in force at a step inside a sub-run. Guarded, its only
counterexample is the ordering defect itself, which is what `LateProbes.Ordering` charges. -/
def SignerDigestFree (adversary : Adversary) : Prop :=
  ∀ pair ∈ support (LateProbes.pairedOf FusedCoverage.fusedTail adversary),
    ∀ entry ∈ pair.2.2.2.2, ∀ framed : Bytes,
      pair.2.2.1 (Hashing.randomizerInput (secretKeyOf pair).prf
          (secretKeyOf pair).publicKey.seed framed) ≠ none →
        entry.1 ≠ Hashing.messageInput
          (HonestProbes.replayRandomizer pair.2.2.1 (secretKeyOf pair) framed)
          (secretKeyOf pair).publicKey framed

set_option maxHeartbeats 1000000 in
/-- **Every target-recorded input is a query the record holds.** -/
theorem hrecord_of_signerDigestFree (adversary : Adversary)
    (hsigner : SignerDigestFree adversary) :
    ∀ pair ∈ support (LateProbes.pairedOf FusedCoverage.fusedTail adversary),
      Target.GoodWalk pair.1 → ∀ entry ∈ pair.2.2.2.2,
        entry.1 ∈ SharedJoin.recordOf (LateProbes.forgetRecordings pair) := by
  classical
  intro pair hpair hgood entry hentry
  obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := LateProbes.mem_support_pairedOf hpair
  subst hvalue
  rw [FusedCoverage.fusedTail] at hresult
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  -- The entry is of the narrowed class, at the walk's key.
  have hnarrow : SplitWitness.narrowClass walk.1.1.2.1
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) entry.1 :=
    SplitPrefix.right_record_class (FusedCoverage.leftKeepAt walk) (FusedCoverage.rightKeepAt walk)
      (SplitWitness.narrowClass walk.1.1.2.1
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
      (fun input inner hkeep => SplitWitness.Served.targetKeep_narrow _ _ input inner hkeep)
      _ (walk.2, [], []) result hresult (by simp) entry hentry
  -- It was absent from the walk's cache and is present at the run's.
  have hfreshwalk : walk.2 entry.1 = none :=
    CoverageTail.walk_cache_fresh _ hpublic withinBounds_structural hwalk entry.1 hnarrow.1
  have hpresent : result.2.1 entry.1 ≠ none :=
    (SplitPrefix.right_record_fresh_nodup (FusedCoverage.leftKeepAt walk)
      (FusedCoverage.rightKeepAt walk) _ (walk.2, [], []) result hresult (by simp) (by simp)).1
      entry hentry
  -- The run, read without its recordings.
  have hrom : (result.1, result.2.1) ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) :=
    SplitPrefix.mem_support_rom _ _ _ (walk.2, [], []) result hresult
  obtain ⟨keys, hkeys, hprov⟩ :=
    provenance_recordedAfterSeeds adversary walk.1.1 walk.2 (result.1, result.2.1) hrom
  have hsk : keys.1 = secretKeyOf (walk, result) := congrArg Prod.fst hkeys
  rcases hprov entry.1 hfreshwalk hpresent with hmem | hkeygen | ⟨request, hrequest, hmade⟩
  · exact hmem
  · obtain ⟨randomizer, message, hinput⟩ := hnarrow.1
    obtain ⟨parent, hparent⟩ :=
      HonestProbes.probes_keygenInternal result.2.1 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
        entry.1 hkeygen
    exact absurd (hinput ▸ hparent)
      (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
  · cases hframe : request.1.frame with
    | none =>
      exact absurd (HonestProbes.probes_sign_none result.2.1 keys.1 request.1 hframe
        (fun _ => False) entry.1 hmade.1) id
    | some framed =>
      rcases HonestProbes.probes_sign result.2.1 keys.1 request.1 framed hframe entry.1
          hmade.1 with ⟨parent, hparent⟩ | hmessage
      · obtain ⟨randomizer, message, hinput⟩ := hnarrow.1
        exact absurd (hinput ▸ hparent)
          (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
      · rcases hmessage with hrandomiser | hdigest
        · refine absurd ⟨keys.1.publicKey.seed, framed, ?_⟩ hnarrow.2
          rw [hrandomiser, show keys.1.prf = walk.1.1.2.1 from by
            rw [hkeys]; exact keygen_prf result.2.1 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2]
        · refine absurd ?_ (hsigner (walk, result) hpair entry hentry framed ?_)
          · rw [hdigest, hsk]
          · rw [← hsk]
            exact hmade.2 framed hframe

end SlhDsaSecurity.LateProvenance

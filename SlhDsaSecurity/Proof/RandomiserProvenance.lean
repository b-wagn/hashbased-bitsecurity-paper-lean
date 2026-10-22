import SlhDsaSecurity.Proof.PhaseProvenance
import SlhDsaSecurity.Proof.RandomiserCharge
import SlhDsaSecurity.Proof.SigningFaithful

/-!
# Who made the randomiser defect's entry

`ReplayGate.RandomiserBad` is the run's final cache holding a `PRF_msg` entry at the real seed,
for a framing no signing request produced. `RandomiserCharge` and `VerifierFormat` rule each
honest party out of making such a query; `CacheProvenance` and `PhaseProvenance` say an entry
that was not there before was made by *someone*. This file puts the two together on the game.

The run is split at its three sequencing points, and the entry is attributed to the first phase
whose cache holds it. Key generation cannot have made it — a canonical input opens with
`PK.seed`, a `PRF_msg` input with `SK.prf`, and the two differ on a good walk. The signer can
only have made it for a request that framed to *this* message, which the event excludes.
The verifier's calls are all `Hashing.tweakable` at `PK.seed` but one. So what is left is the
adversary's own query, which the record carries.

**Except for the overlap, which is carried rather than dismissed.** A message input *is* a
`PRF_msg` input, at its own randomiser read as the seed
(`RandomizerGate.messageInput_eq_randomizerInput`), so the signer's digest query and the
verifier's digest query each match this event's input exactly when the randomiser behind them is
`SK.prf` itself. Neither is a hole and neither is free: the signer's is one coincidence per
request, paid at `2 ^ -128` out of the same budget by `RandomizerGate.prob_randomizerHitsSeed_run_le`,
and the verifier's is the forgery's own randomiser hitting the seed, one more guess. A
provenance argument that forgot the overlap would look like it closed and would not, so the
conclusion names it as a second case.

The conclusion is therefore a two-way split, and the first half is the record — a `Multiset`,
bounded by `Outcome.counts.work`, whose `Multiset.toFinset` is the `Finset Bytes` with a
cardinality cap that `RandomizerGate.prob_run_randomizerInput_le` consumes.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomiserProvenance

open Security CacheReplay RecordedQueries CacheProvenance PhaseProvenance

/-! ## The honest parties, at the signer the game actually runs

`RandomiserCharge` states its two honest lemmas at the *stripped* computations, because that is
what the input half runs. Here the signer is `Scheme.sign` itself, so the stripping step is not
taken and `HonestProbes` applies directly. -/

/-- **Key generation makes no `PRF_msg` query at a foreign seed.** -/
theorem keygen_not_randomizerInput (current : QueryCache HashSpec)
    (secretSeed prfSeed publicSeed : Digest) (prf seed : Digest) (message : Bytes)
    (hne : prf ≠ publicSeed)
    (hprobe : QueriesUnder current
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      (Hashing.randomizerInput prf seed message)) : False := by
  obtain ⟨parent, hparent⟩ :=
    HonestProbes.probes_keygenInternal current secretSeed prfSeed publicSeed _ hprobe
  exact HashSeparation.randomizer_tweakable_ne hne hparent

/-- **A `PRF_msg` query of the signer's is one its own request names.** -/
theorem sign_messageProbe (current : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (prf seed : Digest) (message : Bytes) (hne : prf ≠ sk.publicKey.seed)
    (hprobe : QueriesUnder current (Scheme.sign (m := OracleComp HashSpec) sk request)
      (Hashing.randomizerInput prf seed message)) :
    ∃ framed : Bytes, request.frame = some framed ∧
      HonestProbes.MessageProbe current sk framed
        (Hashing.randomizerInput prf seed message) := by
  cases hframe : request.frame with
  | none =>
    exact absurd
      (HonestProbes.probes_sign_none current sk request hframe (fun _ => False) _ hprobe) id
  | some framed =>
    refine ⟨framed, rfl, ?_⟩
    rcases HonestProbes.probes_sign current sk request framed hframe _ hprobe with
      ⟨parent, hparent⟩ | hmessage
    · exact absurd hparent.symm (RandomizerGate.canonicalInput_ne_randomizerInput
        sk.publicKey.seed prf seed _ parent message hne)
    · exact hmessage

/-! ## The game, split at its three sequencing points -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-- **Where an entry the game installed came from.** The record is the adversary's own hash
inputs; the other three cases name the phase that consulted it, read at the run's own final
cache. -/
theorem provenance_afterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary sds))).run cache))
    :
    ∃ (keys : SecretKey × PublicKey) (record : Multiset Bytes),
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      Multiset.card record ≤ result.1.1.counts.work ∧
      ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
      (probe ∈ record ∨
        QueriesUnder result.2
          (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
        (∃ entry ∈ result.1.1.signed, SignerMade keys.1 result.2 entry.1 probe) ∨
        QueriesUnder result.2
          (Scheme.verify (m := OracleComp HashSpec) keys.2 result.1.1.forgery.message
            result.1.1.forgery.signature) probe) := by
  unfold WarmedGame.afterSeeds at hresult
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
    WarmedSplit.mem_support_of_countQueries _ _ _ _ hverify
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
  -- The record the adversary's phase leaves, and its size.
  obtain ⟨recorded, hrecorded, -, hrecLog', hrecCache', hrecForget⟩ :=
    exists_recorded_of_mem_countedRun sk (adversary.main pk) [] keyCache (value, advCache) hadv
  have hrecLog : recorded.1.2 = value.2 := hrecLog'
  have hrecCache : recorded.2 = advCache := hrecCache'
  have hcounts : (Multiplicative.toAdd recorded.1.1.2).1 = Multiplicative.toAdd value.1.2 :=
    congrArg Multiplicative.toAdd hrecForget
  have hcard : Multiset.card (Multiplicative.toAdd recorded.1.1.2).2 ≤
      result.1.1.counts.work := by
    rw [card_eq_work_adversary (Scheme.sign sk) (adversary.main pk) [] keyCache recorded hrecorded,
      hcounts, houtcome]
    show (Multiplicative.toAdd value.1.2).work ≤
      ((Multiplicative.toAdd value.1.2) + verified.2).work
    rw [AdversaryQueries.work_add]
    exact Nat.le_add_right _ _
  have hkeyreplay : (sk, pk) = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2 := by
    rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
    exact WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ cache keyCache result.2 (sk, pk)
      hkeys hkeyGrow
  refine ⟨(sk, pk), (Multiplicative.toAdd recorded.1.1.2).2, hkeyreplay, hcard, ?_⟩
  intro probe hfresh hpresent
  -- Attribute the entry to the first phase whose cache holds it.
  by_cases hkeyFresh : keyCache probe = none
  · by_cases hadvFresh : advCache probe = none
    · -- Only verification is left.
      refine Or.inr (Or.inr (Or.inr ?_))
      rw [show result.1.1.forgery = value.1.1 from by rw [houtcome]]
      exact queriesUnder_verify_of_fresh pk value.1.1.message value.1.1.signature advCache
        verifyFinal result.2 verified.1 hverifyRun
        (fun input output hentry => by rw [hcache]; exact hentry) probe hadvFresh
        (by rw [hcache] at hpresent; exact hpresent)
    · -- The adversary's phase installed it.
      rcases provenance_phase_subset sk (adversary.main pk) [] keyCache recorded hrecorded
        result.2 (fun input output hentry => hadvGrow input output (by rw [← hrecCache]; exact hentry))
        probe hkeyFresh (by rw [hrecCache]; exact hadvFresh) with hmem | ⟨entry, hentry, hquery⟩
      · exact Or.inl hmem
      · refine Or.inr (Or.inr (Or.inl ⟨entry, ?_, hquery⟩))
        rw [show result.1.1.signed = value.2 from by rw [houtcome]]
        rw [hrecLog] at hentry
        exact hentry
  · -- Key generation installed it.
    exact Or.inr (Or.inl (queriesUnder_keygenInternal_of_fresh sds.1 sds.2.1 sds.2.2 cache
      keyCache result.2 (sk, pk) hkeys hkeyGrow probe hfresh hkeyFresh))

/-! ## The randomiser defect, attributed

With the provenance in hand the four closure lemmas do the rest. Key generation's probes are
canonical and open with `PK.seed`; the signer's `PRF_msg` probe is at its own request's framing,
which the defect excludes because that request is in the log; the verifier's probes are
tweakable at `PK.seed` bar its one digest call. What survives is the adversary's own query — or
the digest overlap, which is carried.

**The overlap has two sources and they are charged differently.** The verifier's is the
forgery's own randomiser being `SK.prf`, which is one guess at the seed and nothing more; so it
is folded into the record as one extra element rather than named as a separate case, and the
same deferral that pays for the adversary's own queries pays for it at one more unit. The
signer's is an *answer* hitting the seed — the randomiser it derived for a request it served
happening to be `SK.prf` — and that is a different kind of event, chargeable against the run's
own randomness without any deferral, so it is named and charged separately below.

`Target.GoodWalk` supplies the walk's own coincidence the argument spends: the two seeds
differ, which is what makes `PRF_msg` and tweakable inputs disjoint, and it is already charged
by `Target.prob_bad_walk`. -/

/-- **The signer's coincidence.** The randomiser the signer derived for a request it served is
the seed itself.

Stated at the *cache entry* the answer sits in, not at `HonestProbes.replayRandomizer`, and the
difference matters: `replay` answers `default` at an absent input, so the predicate read through
`replayRandomizer` alone would also be satisfied by `Hashing.truncate default = SK.prf`, a
statement about a fixed constant that no per-run charge can pay for. The entry's presence comes
from the signing sub-run, through `PhaseProvenance.SignerMade`. -/
def SignerHitsSeed (prfSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (signed : SigningLog) : Prop :=
  ∃ entry ∈ signed, ∃ (framed : Bytes) (answer : HashOutput),
    entry.1.frame = some framed ∧
      cache (Hashing.randomizerInput prfSeed publicSeed framed) = some answer ∧
        Hashing.truncate answer = prfSeed

/-- **A signer coincidence is an answer that hits the seed**, in the form the charge reads. -/
theorem bad_of_signerHitsSeed (prfSeed publicSeed : Digest) (cache : QueryCache HashSpec)
    (signed : SigningLog) {α : Type} (value : α)
    (hhit : SignerHitsSeed prfSeed publicSeed cache signed) :
    GrowthCharge.Bad (RandomizerGate.RandomizerHitsSeed prfSeed) (value, cache) := by
  obtain ⟨entry, -, framed, answer, -, hentry, htruncate⟩ := hhit
  exact ⟨_, answer, hentry, ⟨publicSeed, framed, rfl⟩, htruncate⟩

/-- The one input the forgery's own digest query names, when the forgery has one.

Adding it to the record is how the verifier's half of the overlap is charged. The forgery's
randomiser being `SK.prf` is *exactly* this input being a `PRF_msg` input at the seed, so it is
one more guess at the seed and costs one more unit of the record's cap — no separate argument,
and nothing for the deferral to be told about beyond the cap. -/
noncomputable def forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) : Multiset Bytes :=
  match forgery.message.frame with
  | none => 0
  | some framed =>
    match Signature.fromBytes? forgery.signature with
    | none => 0
    | some parsed => {Hashing.messageInput parsed.randomizer pk framed}

theorem card_forgeryDigestRecord_le (pk : PublicKey) (forgery : Forgery) :
    Multiset.card (forgeryDigestRecord pk forgery) ≤ 1 := by
  unfold forgeryDigestRecord
  split
  · simp
  · split <;> simp

theorem mem_forgeryDigestRecord (pk : PublicKey) (forgery : Forgery) (framed : Bytes)
    (parsed : Signature) (hframe : forgery.message.frame = some framed)
    (hparsed : Signature.fromBytes? forgery.signature = some parsed) :
    Hashing.messageInput parsed.randomizer pk framed ∈ forgeryDigestRecord pk forgery := by
  simp only [forgeryDigestRecord, hframe, hparsed]
  simp

/-! ## How many inputs of the class a run can hold

The charge's rate is the growth of the `PRF_msg` class at the real seed, so what it costs is how
many such entries a run can install. Provenance answers that exactly: every one is the
adversary's own recorded query, or one of the **two** inputs a served request names — its
randomiser's and its digest's — or the forgery's own digest. Key generation is ruled out
because a canonical input opens with `PK.seed`, and the verifier's other calls because they are
tweakable at `PK.seed`.

So the growth is the record's `PRF_msg` part, plus twice the served requests, plus one for the
forgery. The first and last of those are the randomiser defect's *own* charge, which is what
makes the two terms partition rather than add: on a run where no recorded input is of the class
and the forgery's digest is not either, the growth is `2 · served` and nothing more.

The two-per-request is not slack to be squeezed to one. A served request's digest input *is* an
input of the class, at its own randomiser read as the seed, exactly when the coincidence being
charged has already fired at that request. So the second unit is only ever spent on a request
that has already lost, but it cannot be dropped: the growth bound would be false without it,
and a growth bound that is false is worse than a rate that is twice as large. -/

open scoped Classical in
/-- The at most two inputs of the class one logged entry can name. Empty unless the request was
served, which is what keeps the count on the served requests rather than on all of them. -/
noncomputable def entryCandidates (sk : SecretKey) (cache : QueryCache HashSpec)
    (entry : (t : Message) × Option Bytes) : Finset Bytes :=
  if entry.2.isSome then
    entry.1.frame.elim ∅ fun framed =>
      {Hashing.randomizerInput sk.prf sk.publicKey.seed framed,
        Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed) sk.publicKey framed}
  else ∅

open scoped Classical in
theorem entryCandidates_eq (sk : SecretKey) (cache : QueryCache HashSpec)
    (entry : (t : Message) × Option Bytes) (framed : Bytes)
    (hserved : entry.2.isSome) (hframe : entry.1.frame = some framed) :
    entryCandidates sk cache entry =
      {Hashing.randomizerInput sk.prf sk.publicKey.seed framed,
        Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed) sk.publicKey
          framed} := by
  rw [entryCandidates, if_pos hserved, hframe]
  rfl

open scoped Classical in
theorem card_entryCandidates_le (sk : SecretKey) (cache : QueryCache HashSpec)
    (entry : (t : Message) × Option Bytes) :
    (entryCandidates sk cache entry).card ≤ if entry.2.isSome = true then 2 else 0 := by
  rw [entryCandidates]
  by_cases hserved : entry.2.isSome = true
  · rw [if_pos hserved, if_pos hserved]
    cases entry.1.frame with
    | none => simp
    | some framed => exact le_trans (Finset.card_insert_le _ _) (by simp)
  · rw [if_neg hserved, if_neg hserved, Finset.card_empty]

open scoped Classical in
/-- Every input of the class a run can hold: the adversary's own recorded ones that are of the
class, and the two each served request names. The forgery's own digest is expected to be in the
record already, which is where `randomiserBad_source` puts it. -/
noncomputable def prfCandidates (prfSeed : Digest) (sk : SecretKey)
    (cache : QueryCache HashSpec) (record : Multiset Bytes) (signed : SigningLog) :
    Finset Bytes :=
  record.toFinset.filter (RandomizerGate.PrfClass prfSeed) ∪
    signed.toFinset.biUnion (entryCandidates sk cache)

open scoped Classical in
theorem card_prfCandidates_le (prfSeed : Digest) (sk : SecretKey)
    (cache : QueryCache HashSpec) (record : Multiset Bytes) (signed : SigningLog) :
    (prfCandidates prfSeed sk cache record signed).card ≤
      (record.toFinset.filter (RandomizerGate.PrfClass prfSeed)).card +
        2 * AdversaryQueries.servedCount signed := by
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_sum fun entry _ => card_entryCandidates_le sk cache entry) ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  refine Nat.mul_le_mul_left 2 ?_
  rw [AdversaryQueries.servedCount, ← List.toFinset_filter]
  exact List.toFinset_card_le _

open scoped Classical in
/-- **Every input of the class a run installs is one of the candidates.** Key generation cannot
have made it — a canonical input opens with `PK.seed` — and the verifier's calls other than its
one digest are tweakable at `PK.seed`, so what is left is the record, or a served request's own
two inputs. -/
theorem mem_prfCandidates (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (keys : SecretKey × PublicKey) (record : Multiset Bytes)
    (hkeys : keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2)
    (hprov : ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
      (probe ∈ record ∨
        QueriesUnder result.2
          (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
        (∃ entry ∈ result.1.1.signed, SignerMade keys.1 result.2 entry.1 probe) ∨
        QueriesUnder result.2
          (Scheme.verify (m := OracleComp HashSpec) keys.2 result.1.1.forgery.message
            result.1.1.forgery.signature) probe))
    (hforgery : ∀ input ∈ forgeryDigestRecord keys.2 result.1.1.forgery, input ∈ record)
    (hne : sds.2.1 ≠ sds.2.2)
    (hserved : ∀ entry ∈ result.1.1.signed, ∀ framed : Bytes,
      entry.1.frame = some framed → entry.2.isSome)
    (probe : Bytes) (hclass : RandomizerGate.PrfClass sds.2.1 probe)
    (hfresh : cache probe = none) (hpresent : result.2 probe ≠ none) :
    probe ∈ prfCandidates sds.2.1 keys.1 result.2 record result.1.1.signed := by
  have hclass' := hclass
  obtain ⟨seed, payload, rfl⟩ := hclass
  have hkeyseed : keys.1.publicKey.seed = sds.2.2 := by
    rw [hkeys, SigningFaithful.keygen_secretKey]
    exact (GameBridge.keygen_publicKey sds.1 sds.2.1 sds.2.2 result.2).1
  have hpkseed : keys.2.seed = sds.2.2 := by
    rw [hkeys]
    exact (GameBridge.keygen_publicKey sds.1 sds.2.1 sds.2.2 result.2).1
  rcases hprov _ hfresh hpresent with hmem | hkeygen | ⟨entry, hentry, hsign⟩ | hverify
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hmem, hclass'⟩)
  · exact absurd hkeygen fun hquery =>
      keygen_not_randomizerInput result.2 sds.1 sds.2.1 sds.2.2 sds.2.1 seed payload hne hquery
  · refine Finset.mem_union_right _ ?_
    obtain ⟨framed, hframe, hmessage⟩ :=
      sign_messageProbe result.2 keys.1 entry.1 sds.2.1 seed payload
        (by rw [hkeyseed]; exact hne) hsign.1
    refine Finset.mem_biUnion.mpr ⟨entry, List.mem_toFinset.mpr hentry, ?_⟩
    rw [entryCandidates_eq keys.1 result.2 entry framed
      (hserved entry hentry framed hframe) hframe]
    rcases hmessage with hrandomizer | hdigest
    · rw [hrandomizer]
      exact Finset.mem_insert_self _ _
    · rw [hdigest]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · obtain ⟨framed, parsed, hframe, hparsed, hdigest⟩ :=
      VerifierFormat.verify_probe_randomizerInput result.2 keys.2
        result.1.1.forgery.message result.1.1.forgery.signature sds.2.1 seed payload
        (by rw [hpkseed]; exact hne) hverify rfl
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr (hforgery _
        (hdigest ▸ mem_forgeryDigestRecord keys.2 result.1.1.forgery framed parsed hframe
          hparsed)), hclass'⟩)

open scoped Classical in
/-- **The class's growth, sharply.** A duplicate-free list of in-class inputs the run installed
injects into the candidates, so its length is at most their number. -/
theorem growthAtMostOn_prfClass (sds : Digest × Digest × Digest)
    (cache : QueryCache HashSpec) (result : (Outcome × Nat) × QueryCache HashSpec)
    (keys : SecretKey × PublicKey) (record : Multiset Bytes)
    (hkeys : keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      sds.1 sds.2.1 sds.2.2)
    (hprov : ∀ probe : Bytes, cache probe = none → result.2 probe ≠ none →
      (probe ∈ record ∨
        QueriesUnder result.2
          (Scheme.keygenInternal (m := OracleComp HashSpec) sds.1 sds.2.1 sds.2.2) probe ∨
        (∃ entry ∈ result.1.1.signed, SignerMade keys.1 result.2 entry.1 probe) ∨
        QueriesUnder result.2
          (Scheme.verify (m := OracleComp HashSpec) keys.2 result.1.1.forgery.message
            result.1.1.forgery.signature) probe))
    (hforgery : ∀ input ∈ forgeryDigestRecord keys.2 result.1.1.forgery, input ∈ record)
    (hne : sds.2.1 ≠ sds.2.2)
    (hserved : ∀ entry ∈ result.1.1.signed, ∀ framed : Bytes,
      entry.1.frame = some framed → entry.2.isSome) :
    ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass sds.2.1) cache result.2
      ((record.toFinset.filter (RandomizerGate.PrfClass sds.2.1)).card +
        2 * AdversaryQueries.servedCount result.1.1.signed) := by
  intro inputs hnodup hmembers
  have hsub : inputs.toFinset ⊆ prfCandidates sds.2.1 keys.1 result.2 record
      result.1.1.signed := by
    intro input hinput
    rw [List.mem_toFinset] at hinput
    obtain ⟨hclass, hfresh, hpresent⟩ := hmembers input hinput
    exact mem_prfCandidates sds cache result keys record hkeys hprov hforgery hne hserved input
      hclass hfresh hpresent
  calc inputs.length = inputs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (prfCandidates sds.2.1 keys.1 result.2 record result.1.1.signed).card :=
        Finset.card_le_card hsub
    _ ≤ _ := card_prfCandidates_le sds.2.1 keys.1 result.2 record result.1.1.signed

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail

open scoped Classical in
/-- **The randomiser defect is a query at a `PRF_msg` input the run wrote, or the signer's own
randomiser hitting the seed** — and the class's growth is bounded by the record's own part of
it plus twice the served requests.

The first case is a membership in the record — the adversary's own hash inputs together with
the forgery's one digest input — whose `Multiset.toFinset` is the `Finset Bytes` with a
cardinality cap `RandomizerGate.prob_run_randomizerInput_le` consumes. The second is the
signer's coincidence, charged by `prob_signerHitsSeed_tail_le_of_growth` below without any
deferral.

The growth is handed back **with the same record**, which is what lets the two be charged
against disjoint counts rather than against the same one twice: on a run where no recorded
input is of the class — the complement of the first case — the filtered term is zero and the
growth is `2 · served`, so the signer's coincidence costs the served requests and nothing the
record half has already paid for. -/
theorem randomiserBad_source (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hbad : ReplayGate.RandomiserBad ((walk.1, result.1), result.2)) :
    ∃ record : Multiset Bytes, Multiset.card record ≤ result.1.1.counts.work + 1 ∧
      ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass walk.1.1.2.1) walk.2 result.2
        ((record.toFinset.filter (RandomizerGate.PrfClass walk.1.1.2.1)).card +
          2 * AdversaryQueries.servedCount result.1.1.signed) ∧
      ((∃ input ∈ record, RandomizerGate.PrfClass walk.1.1.2.1 input) ∨
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed) := by
  classical
  obtain ⟨message, answer, hentry, hunsigned⟩ := hbad
  set pk := RoutedSplit.keyOf ((walk.1, result.1), result.2) with hpk
  have hseed : pk.seed = walk.1.1.2.2 := by
    rw [hpk]
    exact (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2).1
  have hne : walk.1.1.2.1 ≠ pk.seed := by rw [hseed]; exact hgood.1
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1))).run walk.2) := by
    rw [WarmedGame.tail] at hresult
    exact hresult
  obtain ⟨keys, record, hkeys, hcard, hprovenance⟩ :=
    provenance_afterSeeds adversary walk.1.1 walk.2 result hrun
  have hsource := hprovenance (Hashing.randomizerInput walk.1.1.2.1 pk.seed message)
    (RandomiserCharge.walk_cache_prf_fresh hwalk hgood pk.seed message)
    (by rw [hentry]; exact Option.some_ne_none answer)
  have hkey : keys.2 = pk := by rw [hpk, RoutedSplit.keyOf, SplitCharged.generatedKey, hkeys]
  have hsecret : keys.1 = ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ := by
    rw [hkeys, SigningFaithful.keygen_secretKey, hpk, RoutedSplit.keyOf]
  have hserved : ∀ entry ∈ result.1.1.signed, ∀ framed : Bytes,
      entry.1.frame = some framed → entry.2.isSome := by
    intro entry hentryMem framed hframe
    rw [SigningFaithful.logFaithful_tail adversary hresult entry hentryMem framed hframe]
    rfl
  refine ⟨record + forgeryDigestRecord pk result.1.1.forgery, ?_, ?_, ?_⟩
  · rw [Multiset.card_add]
    exact Nat.add_le_add hcard (card_forgeryDigestRecord_le pk result.1.1.forgery)
  · exact growthAtMostOn_prfClass walk.1.1 walk.2 result keys
      (record + forgeryDigestRecord pk result.1.1.forgery) hkeys
      (fun probe hfresh hpresent =>
        (hprovenance probe hfresh hpresent).imp (fun h => Multiset.mem_add.mpr (Or.inl h)) id)
      (fun input hinput => Multiset.mem_add.mpr (Or.inr (by rw [← hkey]; exact hinput)))
      hgood.1 hserved
  rcases hsource with hmem | hkeygen | ⟨entry, hentryMem, hsign⟩ | hverify
  · exact Or.inl ⟨_, Multiset.mem_add.mpr (Or.inl hmem), pk.seed, message, rfl⟩
  · exact absurd hkeygen fun hquery =>
      keygen_not_randomizerInput result.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
        walk.1.1.2.1 pk.seed message hgood.1 hquery
  · rw [hsecret] at hsign
    obtain ⟨framed, hframe, hmessage⟩ :=
      sign_messageProbe result.2 ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ entry.1 walk.1.1.2.1 pk.seed
        message hne hsign.1
    rcases hmessage with hrandomizer | hdigest
    · obtain ⟨-, -, hequal⟩ := Hashing.randomizerInput_injective hrandomizer
      exact absurd ⟨entry, hentryMem, hequal ▸ hframe⟩ hunsigned
    · refine Or.inr ⟨entry, hentryMem, framed, ?_⟩
      rw [← hseed]
      have hcached : result.2 (Hashing.randomizerInput walk.1.1.2.1 pk.seed framed) ≠ none :=
        hsign.2 framed hframe
      cases hvalue : result.2 (Hashing.randomizerInput walk.1.1.2.1 pk.seed framed) with
      | none => exact absurd hvalue hcached
      | some cached =>
        refine ⟨cached, hframe, rfl, ?_⟩
        have hreplay : HonestProbes.replayRandomizer result.2
            ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ framed = Hashing.truncate cached := by
          rw [HonestProbes.replayRandomizer,
            show CacheReplay.replay result.2
              (Hashing.randomizerInput walk.1.1.2.1 pk.seed framed) = cached from by
              simp [CacheReplay.replay, hvalue]]
        rw [← hreplay]
        exact RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 pk.seed pk
          framed message hdigest.symm
  · obtain ⟨framed, parsed, hframe, hparsed, hdigest⟩ :=
      VerifierFormat.verify_probe_randomizerInput result.2 keys.2 result.1.1.forgery.message
        result.1.1.forgery.signature walk.1.1.2.1 pk.seed message (by rw [hkey]; exact hne)
        hverify rfl
    rw [hkey] at hdigest
    exact Or.inl ⟨Hashing.messageInput parsed.randomizer pk framed,
      Multiset.mem_add.mpr (Or.inr (mem_forgeryDigestRecord pk result.1.1.forgery framed parsed
        hframe hparsed)),
      pk.seed, message, hdigest.symm⟩

/-! ## Charging the signer's coincidence

The signer's half of the overlap is an **answer** hitting the seed, not an input the adversary
chose, so it is charged against the run's own randomness and needs no deferral: a fresh oracle
answer truncates to a fixed digest with probability `2 ^ -128`, and only an input of the
`PRF_msg` class at this seed can fire the event at all.

**What count the charge is against, and what it is not.** It is one unit per fresh query at an
input of that class — *per query, not per request*. Attributing it to requests is wrong, and
not by a constant factor: an adversary that has `SK.prf` hardcoded may query
`randomizerInput SK.prf PK.seed m` for `N` framings of its own choosing, keep the one whose
answer truncates to `SK.prf`, and then make a **single** signing request on that message. The
event fires with probability about `N / 2 ^ 128` with one request logged, so no bound of the
form `(requests) / 2 ^ 128` holds at a fixed walk. The search is free to the attacker in the
sense that matters here: those `N` queries are the adversary's own and are paid for on the
`work` side, not on the signing side.

That attack costs the walk's own randomness — it only works on the walk carrying the hardcoded
seed — so the `requests`-shaped bound may well be *true* once the walk is averaged in. It is
not provable by averaging a per-walk bound, because the per-walk statement it would average is
false. Getting it would need the walk's randomness in the measure, which is the same deferral
`RandomiserDeferral` builds for the record half.

So the charge is stated against the class's own growth, as a parameter, and whoever can bound
that growth chooses the number. `prob_signerHitsSeed_tail_le` instantiates it bluntly at `q`.
The sharp instantiation is the one provenance supports: every in-class entry is the adversary's
own recorded query, or one of the two inputs a served request names, or the forgery's own
digest — so the growth is `(the record's `PRF_msg` part) + 2 · (served requests) + 1`, and the
first and last terms are the randomiser defect's own charge, leaving `2 · served` once that
case is split off.

The walk's cache is clean for the event by `RandomizerGate.cleanBad_of_canonical`: its entries
are canonical, a canonical input opens with `PK.seed`, and the two seeds differ on a good walk.
-/

/-- **The signer's coincidence, with the class's growth read off the run.** This is the shape
the assembly needs rather than the one with the growth as an almost-sure hypothesis: the sharp
growth bound holds only on the branch where the record misses the class, and a conjunct can be
discharged per branch where a hypothesis cannot. The outside limit is needed for the charge's
shape but does not enter the rate, which is why `q` is good enough for it. -/
theorem prob_signerHitsSeed_within_le (adversary : Adversary) (q limit : Nat)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed ∧
          ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass walk.1.1.2.1) walk.2 result.2
            limit |
      WarmedGame.tail adversary walk] ≤ limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [WarmedGame.tail]
  refine le_trans (probEvent_mono ?_)
    (RandomizerGate.prob_randomizerHitsSeed_run_le
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1)) walk.1.1.2.1 walk.2 limit q
      (RandomizerGate.cleanBad_of_canonical walk.1.1.2.2 walk.1.1.2.1 walk.1.2 walk.2 hgood.1
        (WarmedCharges.walk_cache_canonical hwalk)))
  intro result hresult hhit
  have hres : result ∈ support (WarmedGame.tail adversary walk) := by
    rw [WarmedGame.tail]; exact hresult
  have houtside : GrowthCharge.GrowthAtMost walk.2 result.2 q :=
    GrowthBudget.GrowthAtMost.mono
      (GrowthBudget.growth_le_count (WarmedGame.afterSeeds adversary walk.1.1) walk.2 result
        hresult)
      (WarmedCharges.count_le_of_budget_tail hbudget hwalk hres)
  exact ⟨bad_of_signerHitsSeed _ _ _ _ result.1 hhit.1, hhit.2,
    ClassCharge.GrowthAtMostOn.of_growthAtMost houtside⟩

/-- **The signer's coincidence, against the growth of its own class**, when that growth is
bounded on the whole support. -/
theorem prob_signerHitsSeed_tail_le_of_growth (adversary : Adversary) (q limit : Nat)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (hgrowth : ∀ result ∈ support (WarmedGame.tail adversary walk),
      ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass walk.1.1.2.1) walk.2 result.2 limit) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed |
      WarmedGame.tail adversary walk] ≤ limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (probEvent_mono fun result hresult hhit => ⟨hhit, hgrowth result hresult⟩)
    (prob_signerHitsSeed_within_le adversary q limit hbudget hwalk hgood)

/-- **The signer's coincidence, at this run's own walk**, with the class's growth bounded
bluntly by the whole growth. -/
theorem prob_signerHitsSeed_tail_le (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed |
      WarmedGame.tail adversary walk] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  prob_signerHitsSeed_tail_le_of_growth adversary q q hbudget hwalk hgood
    fun result hresult => ClassCharge.GrowthAtMostOn.of_growthAtMost
      (GrowthBudget.GrowthAtMost.mono
        (GrowthBudget.growth_le_count (WarmedGame.afterSeeds adversary walk.1.1) walk.2 result
          (by rw [WarmedGame.tail] at hresult; exact hresult))
        (WarmedCharges.count_le_of_budget_tail hbudget hwalk hresult))

/-! ## The same bound at the paired run

The shared obligation is read at `Target.pairedRun`, the walk and the game together, because the
*other* half of the randomiser defect is a guess at `SK.prf` and no per-walk bound for it can
exist: conditioning on the walk fixes the secret, and an adversary that hardcodes a guess wins
with certainty on the walks that carry it.

This half still spends the oracle's own fresh answer rather than a guess at the seed, so the
per-walk bound stands as proved and only has to be averaged. That is
`Averaging.probEvent_bind_pair_le` with `Target.GoodWalk` carried as a conjunct: on a walk that
fails it the event is empty, and on one that meets it the conjunct discharges the hypothesis the
per-walk bound takes. -/

/-- **The signer's coincidence at the paired run, with the class's growth read off the run.**
This is the form the shared obligation is assembled from. -/
theorem prob_signerHitsSeed_paired_within_le (adversary : Adversary) (q limit : Nat)
    (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair => Target.GoodWalk pair.1 ∧
        (SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.signed ∧
          ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass pair.1.1.1.2.1) pair.1.2 pair.2.2
            limit) |
      Target.pairedRun adversary] ≤ limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [Target.pairedRun]
  refine Averaging.probEvent_bind_pair_le WarmedGame.graphWalk (WarmedGame.tail adversary)
    (fun walk result => Target.GoodWalk walk ∧
      (SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed ∧
        ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass walk.1.1.2.1) walk.2 result.2
          limit)) _ ?_
  intro walk hwalk
  by_cases hgood : Target.GoodWalk walk
  · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
      (prob_signerHitsSeed_within_le adversary q limit hbudget hwalk hgood)
  · rw [probEvent_eq_zero fun result _ hbad => hgood hbad.1]
    exact zero_le

/-- **The signer's coincidence at the paired run, against the growth of its own class**, when
that growth is bounded on the whole support. -/
theorem prob_signerHitsSeed_paired_le_of_growth (adversary : Adversary) (q limit : Nat)
    (hbudget : HasTotalBudget adversary q)
    (hgrowth : ∀ walk ∈ support WarmedGame.graphWalk,
      ∀ result ∈ support (WarmedGame.tail adversary walk),
        ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass walk.1.1.2.1) walk.2 result.2
          limit) :
    Pr[fun pair => Target.GoodWalk pair.1 ∧
        SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.signed |
      Target.pairedRun adversary] ≤ limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [Target.pairedRun]
  refine Averaging.probEvent_bind_pair_le WarmedGame.graphWalk (WarmedGame.tail adversary)
    (fun walk result => Target.GoodWalk walk ∧
      SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed) _ ?_
  intro walk hwalk
  by_cases hgood : Target.GoodWalk walk
  · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
      (prob_signerHitsSeed_tail_le_of_growth adversary q limit hbudget hwalk hgood
        (hgrowth walk hwalk))
  · rw [probEvent_eq_zero fun result _ hbad => hgood hbad.1]
    exact zero_le

/-- **The signer's coincidence, at the paired run**, at the blunt instantiation. -/
theorem prob_signerHitsSeed_paired_le (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair => Target.GoodWalk pair.1 ∧
        SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.signed |
      Target.pairedRun adversary] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  prob_signerHitsSeed_paired_le_of_growth adversary q q hbudget
    fun walk hwalk result hresult => ClassCharge.GrowthAtMostOn.of_growthAtMost
      (GrowthBudget.GrowthAtMost.mono
        (GrowthBudget.growth_le_count (WarmedGame.afterSeeds adversary walk.1.1) walk.2 result
          (by rw [WarmedGame.tail] at hresult; exact hresult))
        (WarmedCharges.count_le_of_budget_tail hbudget hwalk hresult))

end SlhDsaSecurity.RandomiserProvenance

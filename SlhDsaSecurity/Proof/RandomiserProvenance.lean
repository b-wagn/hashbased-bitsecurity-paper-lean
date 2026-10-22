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
    (probe : Bytes) (hfresh : cache probe = none) (hpresent : result.2 probe ≠ none) :
    ∃ (keys : SecretKey × PublicKey) (record : Multiset Bytes),
      keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
        sds.1 sds.2.1 sds.2.2 ∧
      Multiset.card record ≤ result.1.1.counts.work ∧
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

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail

/-- **The randomiser defect is a query at a `PRF_msg` input the run wrote, or the signer's own
randomiser hitting the seed.**

The first case is a membership in the record — the adversary's own hash inputs together with
the forgery's one digest input — whose `Multiset.toFinset` is the `Finset Bytes` with a
cardinality cap `RandomizerGate.prob_run_randomizerInput_le` consumes. The second is the
signer's coincidence, charged by `prob_signerHitsSeed_tail_le` below without any deferral. -/
theorem randomiserBad_source (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hbad : ReplayGate.RandomiserBad ((walk.1, result.1), result.2)) :
    ∃ record : Multiset Bytes, Multiset.card record ≤ result.1.1.counts.work + 1 ∧
      ((∃ input ∈ record, ∃ (seed : Digest) (payload : Bytes),
          input = Hashing.randomizerInput walk.1.1.2.1 seed payload) ∨
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
  obtain ⟨keys, record, hkeys, hcard, hsource⟩ :=
    provenance_afterSeeds adversary walk.1.1 walk.2 result hrun
      (Hashing.randomizerInput walk.1.1.2.1 pk.seed message)
      (RandomiserCharge.walk_cache_prf_fresh hwalk hgood pk.seed message)
      (by rw [hentry]; exact Option.some_ne_none answer)
  have hkey : keys.2 = pk := by rw [hpk, RoutedSplit.keyOf, SplitCharged.generatedKey, hkeys]
  have hsecret : keys.1 = ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ := by
    rw [hkeys, SigningFaithful.keygen_secretKey, hpk, RoutedSplit.keyOf]
  refine ⟨record + forgeryDigestRecord pk result.1.1.forgery, ?_, ?_⟩
  · rw [Multiset.card_add]
    exact Nat.add_le_add hcard (card_forgeryDigestRecord_le pk result.1.1.forgery)
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

**The budget it is charged against has to be the total hash count, and that is not a
convenience.** Every served request makes one in-class query, so the number of coincidences on
offer is the number of requests; if that were capped only by `Security.signingLimit` the charge
would be `2 ^ 64 / 2 ^ 128 = 2 ^ -64`, a *constant*, which for small `q` is far larger than the
`q / 2 ^ 127` the theorem allows and would sink it. What makes it proportional to `q` is that a
served request costs at least two counted hashes
(`AdversaryQueries.work_add_served_le_count_signingOracle`), so the requests are paid for out of
`Security.HasTotalBudget`'s cap on the total count like everything else. Bounding the in-class
growth by the total growth is the blunt form of that, and it is enough.

The walk's cache is clean for the event by `RandomizerGate.cleanBad_of_canonical`: its entries
are canonical, a canonical input opens with `PK.seed`, and the two seeds differ on a good walk.
-/

/-- **The signer's coincidence, at this run's own walk.** -/
theorem prob_signerHitsSeed_tail_le (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed |
      WarmedGame.tail adversary walk] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [WarmedGame.tail]
  refine le_trans (probEvent_mono ?_)
    (RandomizerGate.prob_randomizerHitsSeed_run_le
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1)) walk.1.1.2.1 walk.2 q q
      (RandomizerGate.cleanBad_of_canonical walk.1.1.2.2 walk.1.1.2.1 walk.1.2 walk.2 hgood.1
        (WarmedCharges.walk_cache_canonical hwalk)))
  intro result hresult hhit
  have hres : result ∈ support (WarmedGame.tail adversary walk) := by
    rw [WarmedGame.tail]; exact hresult
  have hgrowth : GrowthCharge.GrowthAtMost walk.2 result.2 q :=
    GrowthBudget.GrowthAtMost.mono
      (GrowthBudget.growth_le_count (WarmedGame.afterSeeds adversary walk.1.1) walk.2 result
        hresult)
      (WarmedCharges.count_le_of_budget_tail hbudget hwalk hres)
  exact ⟨bad_of_signerHitsSeed _ _ _ _ result.1 hhit,
    ClassCharge.GrowthAtMostOn.of_growthAtMost hgrowth,
    ClassCharge.GrowthAtMostOn.of_growthAtMost hgrowth⟩

/-! ## The same bound at the paired run

The shared obligation is read at `Target.pairedRun`, the walk and the game together, because the
*other* half of the randomiser defect is a guess at `SK.prf` and no per-walk bound for it can
exist: conditioning on the walk fixes the secret, and an adversary that hardcodes a guess wins
with certainty on the walks that carry it.

This half is different in kind and the distinction is the reason it needs no such repair. What
it spends is the **oracle's own fresh answer** at an input the signer chooses, not a guess at
anything the walk fixed, so no choice of walk biases it and the per-walk bound above is sound as
it stands. All that is left is to average it, which is `Averaging.probEvent_bind_pair_le` with
`Target.GoodWalk` carried as a conjunct: on a walk that fails it the event is empty, and on one
that meets it the conjunct discharges the hypothesis `prob_signerHitsSeed_tail_le` takes. -/

/-- **The signer's coincidence, at the paired run.** -/
theorem prob_signerHitsSeed_paired_le (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair => Target.GoodWalk pair.1 ∧
        SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.signed |
      Target.pairedRun adversary] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [Target.pairedRun]
  refine Averaging.probEvent_bind_pair_le WarmedGame.graphWalk (WarmedGame.tail adversary)
    (fun walk result => Target.GoodWalk walk ∧
      SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed) _ ?_
  intro walk hwalk
  by_cases hgood : Target.GoodWalk walk
  · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
      (prob_signerHitsSeed_tail_le adversary q hbudget hwalk hgood)
  · rw [probEvent_eq_zero fun result _ hbad => hgood hbad.1]
    exact zero_le

end SlhDsaSecurity.RandomiserProvenance

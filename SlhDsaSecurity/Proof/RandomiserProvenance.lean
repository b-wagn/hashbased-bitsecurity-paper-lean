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

open OracleComp OracleSpec

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
        (∃ entry ∈ result.1.1.signed,
          QueriesUnder result.2
            (Scheme.sign (m := OracleComp HashSpec) keys.1 entry.1) probe) ∨
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
the digest overlap, which is carried as the second case.

`Target.GoodWalk` supplies both of the walk's own coincidences the argument spends: the two
seeds differ, which is what makes `PRF_msg` and tweakable inputs disjoint, and it is already
charged by `Target.prob_bad_walk`. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail

/-- **The randomiser defect is the adversary's own `PRF_msg` query, or the digest overlap.**

The first case is a membership in the record, whose `Multiset.toFinset` is the `Finset Bytes`
with a cardinality cap `RandomizerGate.prob_run_randomizerInput_le` consumes. The second is a
message input that *is* this `PRF_msg` input — which, by
`RandomizerGate.messageInput_eq_randomizerInput_iff`, can only happen when the randomiser behind
that digest is `SK.prf` itself, so it is already stated here with the randomiser identified. -/
theorem randomiserBad_source (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hbad : ReplayGate.RandomiserBad ((walk.1, result.1), result.2)) :
    ∃ record : Multiset Bytes, Multiset.card record ≤ result.1.1.counts.work ∧
      ((∃ input ∈ record, ∃ (seed : Digest) (payload : Bytes),
          input = Hashing.randomizerInput walk.1.1.2.1 seed payload) ∨
        ∃ payload framed : Bytes,
          Hashing.randomizerInput walk.1.1.2.1
              (RoutedSplit.keyOf ((walk.1, result.1), result.2)).seed payload =
            Hashing.messageInput walk.1.1.2.1
              (RoutedSplit.keyOf ((walk.1, result.1), result.2)) framed) := by
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
  refine ⟨record, hcard, ?_⟩
  rcases hsource with hmem | hkeygen | ⟨entry, hentryMem, hsign⟩ | hverify
  · exact Or.inl ⟨_, hmem, pk.seed, message, rfl⟩
  · exact absurd hkeygen fun hquery =>
      keygen_not_randomizerInput result.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
        walk.1.1.2.1 pk.seed message hgood.1 hquery
  · rw [hsecret] at hsign
    obtain ⟨framed, hframe, hmessage⟩ :=
      sign_messageProbe result.2 ⟨walk.1.1.1, walk.1.1.2.1, pk⟩ entry.1 walk.1.1.2.1 pk.seed
        message hne hsign
    rcases hmessage with hrandomizer | hdigest
    · obtain ⟨-, -, hequal⟩ := Hashing.randomizerInput_injective hrandomizer
      exact absurd ⟨entry, hentryMem, hequal ▸ hframe⟩ hunsigned
    · refine Or.inr ⟨message, framed, ?_⟩
      rw [hdigest, RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 pk.seed pk
        framed message hdigest.symm]
  · obtain ⟨framed, parsed, -, -, hdigest⟩ :=
      VerifierFormat.verify_probe_randomizerInput result.2 keys.2 result.1.1.forgery.message
        result.1.1.forgery.signature walk.1.1.2.1 pk.seed message (by rw [hkey]; exact hne)
        hverify rfl
    rw [hkey] at hdigest
    refine Or.inr ⟨message, framed, ?_⟩
    rw [hdigest, RandomizerGate.messageInput_eq_randomizerInput_iff _ walk.1.1.2.1 pk.seed pk
      framed message hdigest.symm]

end SlhDsaSecurity.RandomiserProvenance

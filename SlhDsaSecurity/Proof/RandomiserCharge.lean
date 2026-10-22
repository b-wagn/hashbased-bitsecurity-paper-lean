import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.VerifierFormat

/-!
# Where a `PRF_msg` entry can have come from

`ReplayGate.RandomiserBad` is the cache holding a `PRF_msg` entry at the real seed for a framing
no signing request produced. Charging it means finding the query that made it, and the first
step is to rule out the parts of the run that cannot have.

The warm walk is one of them, and that is what this file proves: the walk programs the canonical
graph and nothing else, a canonical input opens with `PK.seed` and a `PRF_msg` input with
`SK.prf`, and the two seeds differ on a good walk. So a `PRF_msg` entry in the final cache was
made during the tail.

The rest of the provenance is not here, and it has one case that is easy to miss. Key generation
makes no `PRF_msg` query, and the signer's own `PRF_msg` query for a request it served is at
that request's framing, which is not this message. But the *digest* queries are a different
matter: a message input **is** a `PRF_msg` input, at its own randomiser read as the seed
(`RandomizerGate.messageInput_eq_randomizerInput`), so a digest query matches this event's input
exactly when the randomiser it was made under is `SK.prf` itself. For the signer that is one
coincidence per request, and since every request costs at least one counted hash it is paid at
one unit of `2 ^ -128` per request out of the same budget; for the verifier it is the forgery's
own randomiser hitting the seed, which is one more guess. Neither is a hole, but a provenance
argument that forgets the overlap will look like it closes and will not.

What it then takes to charge the event is a deferral, and it is worth saying why nothing shorter
will do. The adversary's queries are not independent of `SK.prf` — the randomisers it sees are
truncations of `PRF_msg` answers at that seed — so the seed cannot simply be drawn afterwards.
What is true is that those answers are a random oracle's at inputs the adversary has not queried,
so they are uniform and independent of the seed *unless* it queries one, which is the event being
charged. That is the hybrid `SeedDeferral` describes and does not yet carry along an execution.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RandomiserCharge

open Security CanonicalGraph WarmedGame

/-- **The warm cache holds no `PRF_msg` entry at the walk's own seed.** -/
theorem walk_cache_prf_fresh
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : Target.GoodWalk walk)
    (seed : Digest) (message : Bytes) :
    walk.2 (Hashing.randomizerInput walk.1.1.2.1 seed message) = none := by
  by_contra hpresent
  obtain ⟨parent, hcanonical⟩ := WarmedCharges.walk_cache_canonical hwalk _ hpresent
  exact RandomizerGate.canonicalInput_ne_randomizerInput walk.1.1.2.2 walk.1.1.2.1 seed
    walk.1.2 parent message hgood.1 hcanonical.symm

/-! ## The honest phase, stripped, asks nothing new

Stripping removes the queries the warm table can answer and leaves the rest untouched, so the
stripped computation's probes are among the original's. That is what lets `HonestProbes`'
characterisations be read off the game's own honest phase rather than off the scheme in
isolation. -/

/-- **A stripped computation consults only what the original does.** -/
theorem queriesUnder_of_strip {α : Type} (cache current : QueryCache HashSpec)
    (hsub : StrippedGame.Extends cache current) :
    ∀ (computation : OracleComp HashSpec α) (probe : Bytes),
      CacheReplay.QueriesUnder current
          (simulateQ (StripCached.stripImpl cache) computation) probe →
        CacheReplay.QueriesUnder current computation probe := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro probe hprobe
    rw [simulateQ_pure] at hprobe
    exact absurd hprobe (by rintro ⟨⟩)
  | query_bind input next ih =>
    intro probe hprobe
    have hstripped : simulateQ (StripCached.stripImpl cache)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        StripCached.stripImpl cache input := by simp
    rw [simulateQ_bind, hstripped] at hprobe
    cases hcache : cache input with
    | some value =>
      rw [show StripCached.stripImpl cache input = (pure value : OracleComp HashSpec HashOutput)
          from by simp [StripCached.stripImpl, hcache], pure_bind] at hprobe
      refine CacheReplay.QueriesUnder.tail input probe next ?_
      rw [show CacheReplay.replay current input = value from by
        simp [CacheReplay.replay, hsub input value hcache]]
      exact ih value probe hprobe
    | none =>
      rw [show StripCached.stripImpl cache input =
          (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) from by
        simp [StripCached.stripImpl, hcache]] at hprobe
      rcases HonestProbes.queriesUnder_query_bind_cases hprobe with rfl | htail
      · exact CacheReplay.QueriesUnder.head _ next
      · exact CacheReplay.QueriesUnder.tail input probe next (ih _ probe htail)

/-! ## What the honest phase's `PRF_msg` queries are

With the stripping out of the way, `HonestProbes` settles both honest parties. Key generation
consults canonical inputs only, and a canonical input opens with `PK.seed`. The signer consults
canonical inputs and the two its own framing names — its randomiser's, which is at *that
request's* message, and its digest's, which is a `PRF_msg` input only at its own randomiser. -/

/-- **Key generation makes no `PRF_msg` query at a foreign seed.** -/
theorem keygen_probe_ne_randomizerInput (warm current : QueryCache HashSpec)
    (hsub : StrippedGame.Extends warm current) (sds : Digest × Digest × Digest)
    (prfSeed seed : Digest) (message : Bytes) (hne : prfSeed ≠ sds.2.2)
    (hprobe : CacheReplay.QueriesUnder current (StrippedGame.strippedKeygenHash warm sds)
      (Hashing.randomizerInput prfSeed seed message)) : False := by
  obtain ⟨parent, hparent⟩ :=
    HonestProbes.probes_keygenInternal current sds.1 sds.2.1 sds.2.2 _
      (queriesUnder_of_strip warm current hsub _ _ hprobe)
  exact HashSeparation.randomizer_tweakable_ne hne hparent

/-- **A `PRF_msg` query of the signer's is one its own request names.** -/
theorem sign_probe_messageProbe (warm current : QueryCache HashSpec)
    (hsub : StrippedGame.Extends warm current) (sk : SecretKey) (request : Message)
    (prfSeed seed : Digest) (message : Bytes) (hne : prfSeed ≠ sk.publicKey.seed)
    (hprobe : CacheReplay.QueriesUnder current (StrippedGame.strippedSignHash warm sk request)
      (Hashing.randomizerInput prfSeed seed message)) :
    ∃ framed : Bytes, request.frame = some framed ∧
      HonestProbes.MessageProbe current sk framed
        (Hashing.randomizerInput prfSeed seed message) := by
  have htransfer := queriesUnder_of_strip warm current hsub _ _ hprobe
  cases hframe : request.frame with
  | none =>
    exact absurd
      (HonestProbes.probes_sign_none current sk request hframe (fun _ => False) _ htransfer) id
  | some framed =>
    refine ⟨framed, rfl, ?_⟩
    rcases HonestProbes.probes_sign current sk request framed hframe _ htransfer with
      ⟨parent, hparent⟩ | hmessage
    · exact absurd hparent.symm (RandomizerGate.canonicalInput_ne_randomizerInput
        sk.publicKey.seed prfSeed seed _ parent message hne)
    · exact hmessage

/-- **The honest phase makes this `PRF_msg` query only as a digest query.** Key generation
cannot make it at all; the signer can only make it for a request that framed to this message,
which is excluded, or as the digest query its framing names — and that one is a `PRF_msg` input
only through the format overlap, with its own randomiser read as the seed. -/
theorem honest_probe_randomizerInput (warm current : QueryCache HashSpec)
    (hsub : StrippedGame.Extends warm current) (sk : SecretKey)
    (hne : sk.prf ≠ sk.publicKey.seed) (message : Bytes)
    (hprobe :
      (∃ sds : Digest × Digest × Digest, sds.2.2 = sk.publicKey.seed ∧
        CacheReplay.QueriesUnder current (StrippedGame.strippedKeygenHash warm sds)
          (Hashing.randomizerInput sk.prf sk.publicKey.seed message)) ∨
      (∃ request : Message, request.frame ≠ some message ∧
        CacheReplay.QueriesUnder current (StrippedGame.strippedSignHash warm sk request)
          (Hashing.randomizerInput sk.prf sk.publicKey.seed message))) :
    ∃ (randomizer : Digest) (framed : Bytes),
      Hashing.randomizerInput sk.prf sk.publicKey.seed message =
        Hashing.messageInput randomizer sk.publicKey framed := by
  rcases hprobe with ⟨sds, hseed, hkeygen⟩ | ⟨request, hrequest, hsign⟩
  · exact absurd hkeygen fun hquery =>
      keygen_probe_ne_randomizerInput warm current hsub sds sk.prf sk.publicKey.seed message
        (hseed ▸ hne) hquery
  · obtain ⟨framed, hframe, hmessage⟩ :=
      sign_probe_messageProbe warm current hsub sk request sk.prf sk.publicKey.seed message hne
        hsign
    rcases hmessage with hrandomizer | hdigest
    · obtain ⟨-, -, hequal⟩ := Hashing.randomizerInput_injective hrandomizer
      exact absurd (hequal ▸ hframe) hrequest
    · exact ⟨_, framed, hdigest⟩

end SlhDsaSecurity.RandomiserCharge

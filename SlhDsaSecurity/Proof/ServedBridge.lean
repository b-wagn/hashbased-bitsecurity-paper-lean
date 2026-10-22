import SlhDsaSecurity.Proof.ServedLog
import SlhDsaSecurity.Proof.ServingCarrier
import SlhDsaSecurity.Proof.CacheProvenance
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.AddressBounds
import SlhDsaSecurity.Proof.SigningFaithful

/-!
# The carrier's served set and the log's, where they meet

The input half's charge reads availability at the handler's carrier; the extraction's events
read disclosure from the signing log, which is in the `Outcome` already. The two have to be the
same object where they meet, and this file is that bridge: what has to hold, which direction
each side needs, and the one `Scheme.sign` fact the agreement turns on.

**They are not equal as the carrier is currently specified, and the obstacle is one clause.**
`ServingCarrier.FilesLeft` requires the query to be **fresh**. A request whose digest input is
already in the cache when the signer asks is therefore served and never filed, so
`ServedLog.servedLog` holds of it and `ServingCarrier.Served` does not. Dropping the freshness
clause closes the gap — the handler sees cached queries too, and nothing else in `FilesLeft`
depends on freshness — and with it dropped the two agree on a good walk. The clause is there
because the recorder wants freshness anyway, which is a reason to record at fresh queries, not a
reason to *file* only at them.

**Which direction each side needs, so the asymmetry is on the record.** The composition needs
`Served ⊆ servedLog`: a smaller served set makes more cells unavailable, hence a bigger
`InputBad`, so the charge covers the extraction's event exactly when the carrier serves no more
than the log does. That direction survives the freshness clause. The *other* direction is what
the carrier's own blindness argument needs — the signer's own reads must be available at the
carrier, or the stalled run reads a cell it must be blind to — and that is the one the clause
breaks. So the clause does not endanger the join; it endangers the charge whose carrier it is.

**What the agreement turns on.** A filed input is a query the signer made while serving a
framing, of that framing's own digest shape. For it to be the log's served input, the randomiser
in it has to be the one the signer published — and `sign_messageShape_randomizer` is that: on a
good walk the digest query is the *only* query `Scheme.sign` makes of that shape. The randomiser
query is excluded by length, the structural queries by `HashSeparation`, and nothing else is
left. This is a fact about `Scheme.sign`, so it holds at every moment of a request and needs no
run.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedBridge

open Security CacheReplay

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  Scheme.sign Scheme.keygenInternal Scheme.verify

/-! ## The one `Scheme.sign` fact the agreement turns on -/

/-- A request's own randomiser input is not of its own digest shape: the digest input carries
`PK.root` before the framing and the randomiser input does not, so they differ in length. -/
theorem randomizerInput_ne_messageInput (prf randomizer : Digest) (pk : PublicKey)
    (framed : Bytes) :
    Hashing.randomizerInput prf pk.seed framed ≠
      Hashing.messageInput randomizer pk framed := by
  intro heq
  rw [RandomizerGate.messageInput_eq_randomizerInput] at heq
  obtain ⟨-, -, hframed⟩ := Hashing.randomizerInput_injective heq
  have hlength := congrArg List.length hframed
  rw [List.length_append, length_bytesBE] at hlength
  have hn : 0 < n := by decide
  omega

/-- **The signer's only query of its own request's digest shape is its digest query.**

So an input filed while that request is being served carries the randomiser the signer derived,
which is the one its published signature holds. The structural queries are excluded by
`HashSeparation` once the key is no coincidence, and the randomiser query by length. -/
theorem sign_messageShape_randomizer (cache : QueryCache HashSpec) (sk : SecretKey)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (randomizer : Digest)
    (hprobe : QueriesUnder cache (Scheme.sign (m := OracleComp HashSpec) sk request)
      (Hashing.messageInput randomizer sk.publicKey framed)) :
    randomizer = HonestProbes.replayRandomizer cache sk framed := by
  rcases HonestProbes.probes_sign cache sk request framed hframe _ hprobe with
    ⟨parent, hparent⟩ | hmessage
  · exact absurd hparent (HashSeparation.message_tweakable_ne hpublic
      (withinBounds_structural parent))
  · rcases hmessage with hrandomiser | hdigest
    · exact absurd hrandomiser.symm (randomizerInput_ne_messageInput sk.prf randomizer
        sk.publicKey framed)
    · exact (Hashing.messageInput_injective hdigest).1

/-! ## The bridge, as the two containments

Stated separately because they are not equally true, and because each side needs only one of
them. `ServedAgree` is the conjunction, which is what a carrier without the freshness clause
should supply. -/

/-- **What the composition needs**: the carrier serves no more than the log does. -/
def CarrierBelowLog (pk : PublicKey) (state : ServingCarrier.Carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∀ input : Bytes, ServingCarrier.Served state input → ServedLog.servedLog pk result input

/-- **What the carrier's own blindness argument needs**: the log serves no more than the carrier
does, so a request the log names has had its digest input filed. This is the direction
`ServingCarrier.FilesLeft`'s freshness clause breaks. -/
def LogBelowCarrier (pk : PublicKey) (state : ServingCarrier.Carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∀ input : Bytes, ServedLog.servedLog pk result input → ServingCarrier.Served state input

/-- The two sets agree. -/
def ServedAgree (pk : PublicKey) (state : ServingCarrier.Carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  CarrierBelowLog pk state result ∧ LogBelowCarrier pk state result

/-! ## What each containment buys

Disclosure is monotone in the served set, so a containment of served sets is a containment of
disclosed positions — which is the form both consumers read. -/

/-- **The carrier's disclosures are among the log's**, given the containment the composition
needs. -/
theorem disclosedAt_subset_disclosedByLog [HasQuery HashSpec Id] (pk : PublicKey)
    (state : ServingCarrier.Carrier) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hbelow : CarrierBelowLog pk state result)
    (hcache : ∀ (input : Bytes) (answer : HashOutput),
      (ServingCarrier.cacheOf state) input = some answer → result.2 input = some answer)
    (key : CanonicalGraph.ForsKey) :
    ServingCarrier.disclosedAt state key ⊆ ServedLog.disclosedByLog pk result key := by
  intro index hindex
  obtain ⟨input, answer, hserved, hentry, hkey, witness⟩ :=
    (ServedDisclosure.mem_servedAt ServingCarrier.Served ServingCarrier.cacheOf state key
      index).mp hindex
  exact (ServedLog.mem_disclosedByLog pk result key index).mpr
    ⟨input, answer, hbelow input hserved, hcache input answer hentry, hkey, witness⟩

/-- **The log's disclosures are among the carrier's**, given the other containment. -/
theorem disclosedByLog_subset_disclosedAt [HasQuery HashSpec Id] (pk : PublicKey)
    (state : ServingCarrier.Carrier) (result : (Outcome × Nat) × QueryCache HashSpec)
    (hbelow : LogBelowCarrier pk state result)
    (hcache : ∀ (input : Bytes) (answer : HashOutput),
      result.2 input = some answer → (ServingCarrier.cacheOf state) input = some answer)
    (key : CanonicalGraph.ForsKey) :
    ServedLog.disclosedByLog pk result key ⊆ ServingCarrier.disclosedAt state key := by
  intro index hindex
  obtain ⟨input, answer, hserved, hentry, hkey, witness⟩ :=
    (ServedLog.mem_disclosedByLog pk result key index).mp hindex
  exact (ServedDisclosure.mem_servedAt ServingCarrier.Served ServingCarrier.cacheOf state key
    index).mpr ⟨input, answer, hbelow input hserved, hcache input answer hentry, hkey, witness⟩

/-! ## The log's side, at a run

What a filed input has to match. `ServedLog.servedLog` asks for a log entry whose answer parses
to a signature whose randomiser the input carries; a logged, served request supplies all three,
and the randomiser it supplies is the one the signer derived — which is
`SigningFaithful.logFaithful_tail` read as a statement about the served set rather than about
bytes. -/

/-- **A log entry serves at its own signature's digest input.** The interface: what a logged
entry gives, with nothing about the run in it. -/
theorem servedLog_of_entry (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (entry : (_ : Message) × Option Bytes) (hentry : entry ∈ result.1.1.signed)
    (framed : Bytes) (hframe : entry.1.frame = some framed)
    (signature : Signature) (hanswer : entry.2 = some signature.toBytes) :
    ServedLog.servedLog pk result (Hashing.messageInput signature.randomizer pk framed) :=
  ⟨entry, hentry, framed, signature.toBytes, signature, hframe, hanswer,
    Signature.fromBytes_toBytes signature, rfl⟩

/-- The randomiser a replayed signature carries is the one the cache replays. -/
theorem signInternal_randomizer (cache : QueryCache HashSpec) (sk : SecretKey)
    (framed : Bytes) :
    (@Scheme.signInternal Id Id.instMonad (replayQuery cache) sk framed).randomizer =
      HonestProbes.replayRandomizer cache sk framed := rfl

/-- **Every logged served request serves at the digest input its own randomiser names.** This is
the target a filed input has to match, and the only thing it asks of the run is that its log be
faithful. -/
theorem servedLog_of_logged (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (entry : (_ : Message) × Option Bytes) (hentry : entry ∈ result.1.1.signed)
    (framed : Bytes) (hframe : entry.1.frame = some framed) :
    ServedLog.servedLog (RoutedSplit.keyOf ((walk.1, result.1), result.2)) result
      (Hashing.messageInput
        (HonestProbes.replayRandomizer result.2
          (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) framed)
        (RoutedSplit.keyOf ((walk.1, result.1), result.2)) framed) := by
  have hfaithful := SigningFaithful.logFaithful_tail adversary hresult entry hentry framed hframe
  rw [← signInternal_randomizer result.2
    (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) framed]
  exact servedLog_of_entry _ result entry hentry framed hframe _ hfaithful

/-! ## The run-level containment

The handler that files does not exist yet, so the containment is stated at what such a handler
has to guarantee rather than at a particular one: every input it serves was a query of the
signer's own sub-run, made while that request's framing was in flight, at a cache the run's own
extends. Those three are the handler's defining property — it files at queries, only while
serving, and the cache only grows — and nothing else about it is used.

**The step to be careful at is the randomiser's two readings.** The filed input carries the
randomiser read at the *filing* cache; the log's entry carries the one read at the *final* one.
They agree because the request's own `PRF_msg` entry is in the cache by the time its digest is
asked for and persists — `CacheProvenance.sign_randomizer_cached`. Both sides spell the
randomiser the same way, which is exactly why the step is easy to skip. -/

/-- **The randomiser a served request names does not move as the cache grows.** -/
theorem replayRandomizer_eq_of_persists (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (initialCache finalCache laterCache : QueryCache HashSpec) (answer : Option Bytes)
    (hmem : (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output) :
    HonestProbes.replayRandomizer finalCache sk framed =
      HonestProbes.replayRandomizer laterCache sk framed := by
  have hcached := CacheProvenance.sign_randomizer_cached sk request framed hframe
    initialCache finalCache finalCache answer hmem (fun _ _ h => h)
  cases hentry : finalCache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) with
  | none => exact absurd hentry hcached
  | some output =>
    rw [HonestProbes.replayRandomizer, HonestProbes.replayRandomizer]
    simp [replay, hentry, hlater _ output hentry]

/-- **What a filing handler guarantees about an input it serves**: it was a query of the
signer's own sub-run, made while that request's framing was in flight, at a cache the run's own
extends, and of that framing's digest shape.

Those four are the handler's defining property — it files at queries, only while serving, the
cache only grows, and the test is the shape — and nothing else about it is used below. Naming
them as one predicate is what lets the containment be stated before any handler exists. -/
def FiledBySigner (sk : SecretKey) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (input : Bytes) : Prop :=
  ∃ entry ∈ result.1.1.signed, ∃ framed : Bytes, entry.1.frame = some framed ∧
    ∃ (initialCache finalCache : QueryCache HashSpec) (answer : Option Bytes),
      (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
        (Scheme.sign sk entry.1 : OracleComp OracleWorld (Option Bytes))).run initialCache) ∧
      (∀ (probe : Bytes) (output : HashOutput),
        finalCache probe = some output → result.2 probe = some output) ∧
      QueriesUnder finalCache (Scheme.sign (m := OracleComp HashSpec) sk entry.1) input ∧
      ∃ randomizer : Digest, input = Hashing.messageInput randomizer pk framed

/-- **The carrier serves no more than the log does**, at a run, from what the filing handler
guarantees and nothing else.

The key and the secret key are taken as parameters tied by equations rather than written out,
which is not cosmetic: spelled out, the statement makes the elaborator chase
`RoutedSplit.keyOf` through key generation at every occurrence, and it does not come back. -/
theorem carrierBelowLog_of_filed (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (sk : SecretKey) (pk : PublicKey)
    (hsk : sk = ReplayGate.secretKeyOf ((walk.1, result.1), result.2))
    (hpk : pk = RoutedSplit.keyOf ((walk.1, result.1), result.2))
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (state : ServingCarrier.Carrier)
    (hfiled : ∀ input : Bytes, ServingCarrier.Served state input →
      FiledBySigner sk pk result input) :
    CarrierBelowLog pk state result := by
  subst hsk
  subst hpk
  intro input hserved
  obtain ⟨entry, hentry, framed, hframe, initialCache, finalCache, answer, hmem, hlater,
    hprobe, randomizer, rfl⟩ := hfiled input hserved
  have hshape : randomizer =
      HonestProbes.replayRandomizer finalCache
        (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) framed :=
    sign_messageShape_randomizer finalCache
      (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) entry.1 framed hframe hpublic
      randomizer hprobe
  rw [hshape, replayRandomizer_eq_of_persists
    (ReplayGate.secretKeyOf ((walk.1, result.1), result.2)) entry.1 framed hframe initialCache
    finalCache result.2 answer hmem hlater]
  exact servedLog_of_logged adversary hresult entry hentry framed hframe

end SlhDsaSecurity.ServedBridge

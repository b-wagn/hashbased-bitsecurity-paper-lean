import SlhDsaSecurity.Proof.ServedLog
import SlhDsaSecurity.Proof.ServingCarrier
import SlhDsaSecurity.Proof.CacheProvenance
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.AddressBounds

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

end SlhDsaSecurity.ServedBridge

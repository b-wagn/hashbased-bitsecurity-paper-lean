import SlhDsaSecurity.Proof.ServedDisclosure
import SlhDsaSecurity.Proof.HonestProbes

/-!
# What a handler has to carry for disclosure to be served-indexed

`ServedDisclosure` states the notion against an abstract state: a `served` predicate naming the
digest inputs the signer has served, and a cache the digests are read from. This file is the
carrier those two are read off, and the three operations a handler performs on it.

**The flag carries the framing, not the request, and the set carries digest inputs, not
messages.** Indexing by the message would let an adversary choose its own randomiser for a
message the signer did sign and have its own digest's positions counted as disclosed — the same
fiction the cache proxy allowed, in a new place. Indexing by the *input* pins the randomiser and
the message together through `Hashing.messageInput_injective`, and the framing in the flag is
what the recorder tests an input against, so an input of the right shape for a *different*
request is not filed.

**Filing happens at the query, not at the request.** The digest input is not known when the
request arrives — it depends on the randomiser the oracle has yet to answer — so the carrier
cannot be told it up front. What the handler can do is set the framing while it serves, and file
an input when a fresh query matches that framing. `FilesLeft` is that test, and it reads the
input and the state and nothing else; the cache clause in it is freshness, which the recorder
needs anyway.

**Why the ordering now holds by construction.** `servedAt_file_cacheQuery` is the statement the
old proxy was standing in for: the step that draws a digest both files its input and caches its
answer, so from that step onwards the positions it selects are disclosed. The signer draws its
digest before it reads any FORS secret, so by the time it reads one the secret is available — and
unlike the proxy, nothing an adversary can do files an input, because only the signing oracle
sets the framing.

The flag itself is invisible to disclosure (`servedAt_setFraming`): it decides what is filed,
never what is disclosed. That is what keeps the stalled charge's availability unchanged by the
bookkeeping.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingCarrier

open CanonicalGraph Security

/-- What a handler carries: the cache, the digest inputs the signer has served, and the framing
of the request it is serving. -/
structure Carrier where
  cache : QueryCache HashSpec
  served : Multiset Bytes
  framing : Option Bytes

/-- The digest inputs a carrier has served. -/
def Served (state : Carrier) (input : Bytes) : Prop := input ∈ state.served

/-- The cache a carrier holds. -/
def cacheOf (state : Carrier) : QueryCache HashSpec := state.cache

/-- The positions a carrier's served requests disclose. -/
noncomputable abbrev disclosedAt (state : Carrier) (key : ForsKey) :
    Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  ServedDisclosure.servedAt Served cacheOf state key

/-! ## The three operations

A handler sets the framing while it serves, files an input it recognises, and caches an answer.
Each is monotone, which is all the charge above needs of them. -/

/-- Growth of a carrier, stated at **what it discloses** and not at its three components.

That is not a stylistic choice. The step in which a request completes takes its framing out of
flight, and a relation that fixed the framing component would fail at exactly that step — the
step the whole notion exists for. So the relation says two things and neither mentions the
framing: entries persist, and served inputs stay served. `grows_of_framing` is the visible form
of that: *any* change of framing is growth. -/
def Grows (left right : Carrier) : Prop :=
  (∀ (input : Bytes) (answer : HashOutput),
      left.cache input = some answer → right.cache input = some answer) ∧
    ∀ input : Bytes, Served left input → Served right input

theorem Grows.refl (state : Carrier) : Grows state state := ⟨fun _ _ h => h, fun _ h => h⟩

theorem Grows.trans {left middle right : Carrier} (hfirst : Grows left middle)
    (hsecond : Grows middle right) : Grows left right :=
  ⟨fun input answer hentry => hsecond.1 input answer (hfirst.1 input answer hentry),
    fun input hinput => hsecond.2 input (hfirst.2 input hinput)⟩

/-- **Disclosure only grows.** This is `ServedDisclosure.servedAt_mono` at the carrier. -/
theorem disclosedAt_mono {left right : Carrier} (hgrow : Grows left right) (key : ForsKey) :
    disclosedAt left key ⊆ disclosedAt right key :=
  ServedDisclosure.servedAt_mono Served cacheOf left right hgrow.2 hgrow.1 key

/-- Set the framing of the request being served. -/
def setFraming (state : Carrier) (framed : Bytes) : Carrier :=
  { state with framing := some framed }

/-- Clear it when the request is done. -/
def clearFraming (state : Carrier) : Carrier := { state with framing := none }

/-- File a digest input the signer has served. -/
def file (state : Carrier) (input : Bytes) : Carrier :=
  { state with served := input ::ₘ state.served }

/-- Cache an answer. -/
def cacheAnswer (state : Carrier) (input : Bytes) (answer : HashOutput) : Carrier :=
  { state with cache := state.cache.cacheQuery input answer }

/-- **Any change of framing is growth.** The relation does not constrain the component, so the
completing step — which takes a request out of flight — is growth like every other. A
componentwise relation would be false here, and this is the lemma that says so. -/
theorem grows_of_framing (state : Carrier) (framing : Option Bytes) :
    Grows state { state with framing := framing } := Grows.refl state

theorem grows_setFraming (state : Carrier) (framed : Bytes) :
    Grows state (setFraming state framed) := grows_of_framing state (some framed)

theorem grows_clearFraming (state : Carrier) : Grows state (clearFraming state) :=
  grows_of_framing state none

theorem grows_file (state : Carrier) (input : Bytes) : Grows state (file state input) :=
  ⟨fun _ _ h => h, fun probe hprobe => Multiset.mem_cons_of_mem hprobe⟩

theorem grows_cacheAnswer (state : Carrier) (input : Bytes) (answer : HashOutput)
    (hfresh : state.cache input = none) : Grows state (cacheAnswer state input answer) := by
  refine ⟨fun probe value hvalue => ?_, fun _ h => h⟩
  by_cases hequal : probe = input
  · rw [hequal, hfresh] at hvalue
    exact absurd hvalue (by simp)
  · show (state.cache.cacheQuery input answer) probe = some value
    rw [QueryCache.cacheQuery_of_ne state.cache answer hequal]
    exact hvalue

/-- **The framing is invisible to disclosure.** It decides what the recorder files, never what
is disclosed, so the charge that stalls on the disclosed set is untouched by it. -/
theorem servedAt_setFraming (state : Carrier) (framed : Bytes) (key : ForsKey) :
    disclosedAt (setFraming state framed) key = disclosedAt state key := rfl

theorem servedAt_clearFraming (state : Carrier) (key : ForsKey) :
    disclosedAt (clearFraming state) key = disclosedAt state key := rfl

/-! ## The ordering, by construction

The step that draws a digest files its input and caches its answer together. From then on the
positions that digest selects are disclosed, and nothing later can take them away. This is what
`RedrawCell.signInternal_congr`'s `hsigned` was asking for and what the cache proxy was standing
in for. -/

/-- **A filed digest discloses its own positions, from the step that drew it.** -/
theorem mem_disclosedAt_file_cacheAnswer (state : Carrier) (input : Bytes)
    (answer : HashOutput) (hfresh : state.cache input = none)
    (tree : Fin forsTrees) :
    GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree ∈
      disclosedAt (file (cacheAnswer state input answer) input)
        (SplitCharged.forsKeyOfDigest answer) := by
  classical
  refine (ServedDisclosure.mem_servedAt Served cacheOf _ _ _).mpr ⟨input, answer, ?_, ?_, rfl,
    tree, rfl⟩
  · exact Multiset.mem_cons_self _ _
  · show (state.cache.cacheQuery input answer) input = some answer
    exact QueryCache.cacheQuery_self state.cache input answer

/-- **And it stays disclosed.** -/
theorem mem_disclosedAt_of_grows {left right : Carrier} (hgrow : Grows left right)
    (key : ForsKey) {index : Fin (forsTrees * 2 ^ forsHeight)}
    (hindex : index ∈ disclosedAt left key) : index ∈ disclosedAt right key :=
  disclosedAt_mono hgrow key hindex

/-! ## The recorder's left test

A fresh query made while the framing names a request, at an input of that request's own digest
shape. It reads the input and the state and nothing else — the cache clause is freshness, which
the recorder wants anyway, and there is no clause an adversary can satisfy, because only the
signing oracle sets the framing. -/

/-- The test the recorder files the disclosing list by. -/
def FilesLeft (pk : PublicKey) (state : Carrier) (input : Bytes) : Prop :=
  state.cache input = none ∧
    ∃ framed : Bytes, state.framing = some framed ∧
      ∃ randomizer : Digest, input = Hashing.messageInput randomizer pk framed

/-- **Nothing is filed when nothing is being served.** The adversary's own queries run with the
framing clear, so the test is false at every one of them whatever they ask. -/
theorem not_filesLeft_of_clear (pk : PublicKey) (state : Carrier)
    (hclear : state.framing = none) (input : Bytes) : ¬ FilesLeft pk state input := by
  rintro ⟨-, framed, hframing, -⟩
  rw [hclear] at hframing
  simp at hframing

/-- **A filed input is the in-flight request's own digest input.** The framing pins the message
and the input pins the randomiser, so nothing of another request's shape is filed. -/
theorem framed_of_filesLeft (pk : PublicKey) (state : Carrier) (input : Bytes)
    (hfiles : FilesLeft pk state input) :
    ∃ (framed : Bytes) (randomizer : Digest), state.framing = some framed ∧
      input = Hashing.messageInput randomizer pk framed := by
  obtain ⟨-, framed, hframing, randomizer, hinput⟩ := hfiles
  exact ⟨framed, randomizer, hframing, hinput⟩

/-! ## The carrier and the trace must agree

The entries a probe is paired with carry whatever availability is read from, so they carry a
carrier; the event `RoutedSplit.InputBad` reads disclosure at the trace, whose record of what was
served is the **log**. Those are two objects and the instantiation needs them to be one. At the
end of a run they are: every completed request is logged and nothing is in flight. Stating it
here, where both sides can see it, is what keeps that from surfacing at the join.
-/

/-- The digest inputs a signing log names, each read at the cache the randomiser is replayed
from. -/
def logServed (sk : SecretKey) (cache : QueryCache HashSpec) (signed : SigningLog)
    (input : Bytes) : Prop :=
  ∃ entry ∈ signed, ∃ framed : Bytes, entry.1.frame = some framed ∧
    input = Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed)
      sk.publicKey framed

/-- **What a run must leave true**: the carrier served exactly what the log names. -/
def AgreesWithLog (sk : SecretKey) (signed : SigningLog) (state : Carrier) : Prop :=
  ∀ input : Bytes, Served state input ↔ logServed sk state.cache signed input

/-- **Under agreement the two readings of disclosure are one `Finset`.** This is what lets the
entries and the event be instantiated at the same object. -/
theorem disclosedAt_eq_logDisclosed (sk : SecretKey) (signed : SigningLog) (state : Carrier)
    (hagree : AgreesWithLog sk signed state) (key : ForsKey) :
    disclosedAt state key =
      ServedDisclosure.servedAt (fun cache => logServed sk cache signed) id state.cache key := by
  classical
  refine Finset.ext fun index => ?_
  rw [ServedDisclosure.mem_servedAt, ServedDisclosure.mem_servedAt]
  constructor
  · rintro ⟨input, answer, hserved, hcache, hkey, tree, htree⟩
    exact ⟨input, answer, (hagree input).mp hserved, hcache, hkey, tree, htree⟩
  · rintro ⟨input, answer, hlog, hcache, hkey, tree, htree⟩
    exact ⟨input, answer, (hagree input).mpr hlog, hcache, hkey, tree, htree⟩

end SlhDsaSecurity.ServingCarrier

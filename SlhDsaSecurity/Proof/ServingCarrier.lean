import SlhDsaSecurity.Proof.ServedDisclosure
import SlhDsaSecurity.Proof.HonestProbes
import SlhDsaSecurity.Proof.HandlerCarrier

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
an input that matches that framing. `HandlerCarrier.FilesLeft` is that test, and it asks for no
freshness: a served request whose digest input was already cached is served all the same, and
leaving it unfiled would make the signer's own reads unavailable at the carrier.

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

/-! ## The type, declared below

The carrier's type and the operations on it live in `HandlerCarrier`, below `OpenCache`, because
the handler that has to carry them is below the files that state what is read off them. The
names are re-exported here so that everything stated at the notion can be read in one place. -/

/-- What a handler carries. -/
abbrev Carrier := HandlerCarrier.State

export HandlerCarrier (Served cacheOf Grows setFraming clearFraming file cacheAnswer
  grows_of_framing grows_setFraming grows_clearFraming grows_file grows_cacheAnswer
  FilesLeft not_filesLeft_of_clear framed_of_filesLeft)

/-- The positions a carrier's served requests disclose. -/
noncomputable abbrev disclosedAt (state : Carrier) (key : ForsKey) :
    Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  ServedDisclosure.servedAt Served cacheOf state key

/-- **Disclosure only grows.** This is `ServedDisclosure.servedAt_mono` at the carrier. -/
theorem disclosedAt_mono {left right : Carrier} (hgrow : Grows left right) (key : ForsKey) :
    disclosedAt left key ⊆ disclosedAt right key :=
  ServedDisclosure.servedAt_mono Served cacheOf left right hgrow.2 hgrow.1 key

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

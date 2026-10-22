import SlhDsaSecurity.Proof.RecorderView

/-!
# The recorder at the carrier, with the flag deciding and the served set remembering

This is the instantiation the parameterisation was for. The disclosing test is
`HandlerCarrier.FilesLeft` — a query made while the signing oracle holds its framing up, at an
input of that request's own digest shape — and the predicate the recording's entries satisfy at
the end is `HandlerCarrier.Served`, membership of the carrier's served multiset.

**The two are different predicates, and the reason is one sentence: a cache-readable test is
monotone because it is forgeable.** `AnswerJoin.hdisclosing` asks
for an iff between the signing log and a *cache-readable* disclosing test, and its right-to-left
direction is false: an adversary holding `SK.prf` can put the `PRF_msg` entry a cache test looks
for into the cache with no request behind it. A flag cannot be forged, because only the signing
oracle sets it — but a flag is down again by the end of the run, so it cannot also be the thing
an entry satisfies at the end. Splitting the roles is what lets the test be unforgeable and the
record be readable at once, and `RecorderView.left_recordOf_endKeep_final` is where the split
is paid for: filing puts the input into the served set, and no later step takes it out.

What remains on the log side is `ServingCarrier.AgreesWithLog` — the served set is the image of
the signing log — which is a fact about the signing oracle rather than an assumption about the
adversary, and is the log thread's. The false direction is gone, not relocated.

**The update files and caches in one step**, which is what `servingUpdate` is. It is a legal
`CacheView` because the law constrains only the cache, and filing does not touch it; that the
law is this weak is what makes the instantiation possible at all.

**A test that reads a flag can only be instantiated at a presentation that sets the flag.** That
is the other face of the rule above: `FilesLeft` is not merely unforgeable, it is *empty*
wherever nothing frames. So the left test and the tail have to move together — a run that reads
the flag over a computation with no bracket in it files nothing, and every question about what
the recording holds answers itself for the wrong reason.

Two gaps between this file and a carrier tail are recorded rather than papered over: the one at
`servingUpdate` below, and that a bracketed run is not a `LateProbes.IsRecorderRun`, since
brackets write the state between queries and no `OracleComp OracleWorld` can.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarriedWitness

open RecorderView HandlerCarrier

variable (pk : PublicKey)

/-! ## The view

Filing and caching in the same step: disclosure begins exactly where the answer does. A design
that filed later would disclose after the signer's own reads, which is the failure this repairs.
-/

open scoped Classical in
/-- Install an answer, and file the input when the flag says the signer is serving it.

**This definition is not yet the one the carrier needs, and the gap is recorded here so that
nothing is built on it.** `RecorderView.recorderOf` calls `CacheView.update` on the *fresh*
branch only — a cache hit returns the cached answer and leaves the state — so filing through the
update files only inputs the run itself drew. That is exactly what `HandlerCarrier.FilesLeft`'s
docstring forbids: a served request whose digest input is already cached is served all the same,
and leaving it unfiled makes the signer's own reads unavailable at the carrier.

The consequence is worse than a missing entry, which is why it is flagged rather than deferred.
Filing only on fresh draws makes the ordering defect **vacuous**: a target-recorded input was
not filed at its own query, it is installed in the cache by that query, so it is never fresh
again, so it can never be filed later and `Served` can never reach it. `Late` would be false by
construction, and the charge that bounds it would look discharged while the case it exists for —
the adversary asking a digest input *before* the request that makes it a served one — had simply
been defined away.

The repair is one more operation on the view, applied at **every** hash query rather than only
at a miss, with the single law that it does not touch the cache — which is all
`run_recorderOf_forget` ever reads. At `σ := QueryCache HashSpec` it is the identity, so the
cache instantiation and `recorderOf_cache` are unaffected. -/
noncomputable def servingUpdate (state : State) (input : Bytes) (answer : HashOutput) : State :=
  if FilesLeft pk state input then file (cacheAnswer state input answer) input
  else cacheAnswer state input answer

open scoped Classical in
/-- **Filing does not touch the cache**, so the view's one law holds. -/
theorem cacheOf_servingUpdate (state : State) (input : Bytes) (answer : HashOutput) :
    cacheOf (servingUpdate pk state input answer) =
      (cacheOf state).cacheQuery input answer := by
  classical
  rw [servingUpdate]
  split <;> rfl

open scoped Classical in
/-- The carrier as a recorder state, with the signing oracle's own update. -/
noncomputable def servingView : CacheView State where
  cacheOf := cacheOf
  update := servingUpdate pk
  cache_update := cacheOf_servingUpdate pk

open scoped Classical in
/-- **A filed input is served from that step on.** -/
theorem served_servingUpdate_self (state : State) (input : Bytes) (answer : HashOutput)
    (hfiles : FilesLeft pk state input) : Served (servingUpdate pk state input answer) input := by
  classical
  rw [servingUpdate, if_pos hfiles]
  exact Multiset.mem_cons_self _ _

open scoped Classical in
/-- **No step unserves anything.** -/
theorem served_servingUpdate (state : State) (input probe : Bytes) (answer : HashOutput)
    (hserved : Served state input) : Served (servingUpdate pk state probe answer) input := by
  classical
  rw [servingUpdate]
  split
  · exact Multiset.mem_cons_of_mem hserved
  · exact hserved

/-! ## The two tests at the carrier -/

/-- The left test: the flag is up for a request, and the input is that request's own digest
shape. Only the signing oracle sets the flag, so there is no clause an adversary can satisfy. -/
def disclosingKeep : Bytes → State → Prop := fun input state => FilesLeft pk state input

/-- What an entry of the disclosing recording satisfies at the end: the carrier served it. -/
def disclosedAtEnd : Bytes → State → Prop := fun input state => Served state input

open scoped Classical in
/-- **Every entry of the disclosing recording was served**, read at the end of the run. The flag
decided each entry when it was filed; the served set is what remembers. -/
theorem mem_served_of_mem_leftRecord {α : Type} (rightKeep : Bytes → State → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf State)
    (result : α × StateOf State)
    (hmem : result ∈ support ((simulateQ
      (@recorderOf State (servingView pk) (disclosingKeep pk) rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.1, Served state.1 entry.1) :
    ∀ entry ∈ result.2.2.1, Served result.2.1 entry.1 :=
  @left_recordOf_endKeep_final State (servingView pk) α (disclosingKeep pk) rightKeep
    (disclosedAtEnd)
    (fun input view answer _ hkeep => served_servingUpdate_self pk view input answer hkeep)
    (fun input probe view answer _ hkeep => served_servingUpdate pk view input probe answer hkeep)
    computation state result hmem hstart

/-! ## What the flag rejects

Both halves of the blindness, at the carrier's own test rather than at the cache. -/

/-- **Nothing the adversary asks is filed**, because its queries run with the flag down. -/
theorem not_disclosingKeep_of_clear (state : State) (hclear : state.framing = none)
    (input : Bytes) : ¬ disclosingKeep pk input state :=
  not_filesLeft_of_clear pk state hclear input

/-- **The signer's own randomiser query is not filed either**, because the flag is matched
against the request in flight and `PRF_msg` at that frame is a message input at a shorter
message. See the warning at `HandlerCarrier.FilesLeft`: a test that only asked whether some
request was in flight would take this query, and the disclosing cap would be lost past the
coupling's mean rather than past its tail. -/
theorem not_disclosingKeep_randomizerInput (state : State) (prfSeed : Digest) (framed : Bytes)
    (hframing : state.framing = some framed) :
    ¬ disclosingKeep pk (Hashing.randomizerInput prfSeed pk.seed framed) state :=
  not_filesLeft_randomizerInput pk state prfSeed framed hframing

/-! ## What the target recording cannot hold

`LateProvenance.SignerDigestFree` says that no target-recorded input is a served request's own
digest input. At a cache-readable left test that is an ordering statement — the signer asks for
its randomiser before its digest, so the entry is already there when the digest query is made —
and nothing reports what the cache held partway through a sub-run, which is why it stands as a
hypothesis.

At the flag there is no ordering. A target-recorded entry comes with the state it was filed
from, and at that state the right test held, hence the left test did not; and the left test is
read off that state's own flag. So the entry cannot be a digest query made under a matching
flag, for the state's reason rather than for the run's. -/

open scoped Classical in
/-- **A target-recorded input is not the digest input of whatever request was in flight when it
was queried.** The whole content is the flag at that state: no ordering to establish, and no
entry of the cache consulted. This is `SignerDigestFree` with the step it is really about named,
and it is the form a bracketed run discharges. -/
theorem not_inflight_digest_of_mem_rightRecord {α : Type} (rightKeep : Bytes → State → Prop)
    (hexclusive : ∀ (input : Bytes) (view : State),
      rightKeep input view → ¬ disclosingKeep pk input view)
    (computation : OracleComp OracleWorld α) (state : StateOf State)
    (result : α × StateOf State)
    (hmem : result ∈ support ((simulateQ
      (@recorderOf State (servingView pk) (disclosingKeep pk) rightKeep) computation).run state))
    (hstart : state.2.2 = []) :
    ∀ entry ∈ result.2.2.2, ∃ mid : State,
      (∀ (probe : Bytes) (value : HashOutput),
        cacheOf mid probe = some value → cacheOf result.2.1 probe = some value) ∧
        cacheOf mid entry.1 = none ∧
          ∀ framed : Bytes, mid.framing = some framed →
            ∀ randomizer : Digest, entry.1 ≠ Hashing.messageInput randomizer pk framed := by
  classical
  intro entry hentry
  rcases @right_recordOf_witness State (servingView pk) α (disclosingKeep pk) rightKeep
    computation state result hmem entry hentry with hold | ⟨mid, hpersist, hfresh, hright⟩
  · rw [hstart] at hold
    simp at hold
  · refine ⟨mid, hpersist, hfresh, fun framed hframing randomizer hshape => ?_⟩
    exact hexclusive entry.1 mid hright ⟨framed, hframing, randomizer, hshape⟩

end SlhDsaSecurity.CarriedWitness

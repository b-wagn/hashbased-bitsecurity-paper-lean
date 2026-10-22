import SlhDsaSecurity.Proof.SplitWitness
import SlhDsaSecurity.Proof.SignerRandomiser

/-!
# The signer's two message-dependent queries, in order

`LateProvenance.SignerDigestFree` was false before it was guarded —
`ObligationShapes.targetKeep_default` and `messageInput_default_eq_replay` refute the unguarded
form, and the guard is the negation of the first's `hcold`, so they no longer apply. The guarded
hypothesis is **open**, and believed false at `2 ^ -128` by an argument that is prose rather
than Lean (see that file's section). Either way the repair is the same: prove its consequence by
provenance instead, so that nothing rests on a hypothesis whose failure set is the defect the
shared half already pays for. Of the four parties, three cases are settled by statements that read the
input alone; the fourth is this file.

**Why the other three need no state and this one does.** "Not message-class" and "in the
`PRF_msg` class at the real seed" are predicates on bytes, so a replay-at-a-fixed-cache
statement like `HonestProbes.probes_signInternal` settles them and the cache never enters. The
signer's *digest* probe is different: whether the target test takes it depends on what the cache
held when it was asked, and that is not a question the replay vocabulary can be asked. Replay is
faithful to a run only at the run's **final** cache — which is the invariant inside
`CacheReplay.cached_of_queriesUnder`, and the reason provenance is stated there — and at any
intermediate cache it diverges, since a miss replays to `default`. That divergence is not a
side issue: it is the whole of the counterexample, where `replayRandomizer` at an unsigned
message fabricates `truncate default`.

**So the fact is proved about the run, and it costs two unfoldings rather than an induction.**
`Scheme.signInternal`'s first two binds are the randomiser query and the digest query, adjacent,
with the digest's randomiser *being* the first query's answer. After the first step the answer
is in the cache — `RecorderView.recorderOf_step_cache_self`, which holds whichever branch the
step took — and the second step's input is `messageInput (truncate answer) pk message`. That is
`SignerRandomised` at that very state, with the existential's witnesses read straight off the
step. No ordering is established, because there is nothing to establish: the two queries are
adjacent in the source.

The consequence is `not_targetKeep_digest`: the left test takes the digest query, so the target
recording cannot hold it as *that* query. An adversary may of course ask the same bytes itself,
and then the entry is the adversary's and sits in the record — which is what the consequence
asks for, and why it survives the counterexample that sank the hypothesis.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SignerDigestStep

open Security CacheAvailability SplitPrefix RecorderView SignerRandomiser

/-! ## The cut, taken twice -/

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `signInternalAt` once its digest is in hand too. -/
def signInternalRest (randomizer : Digest) (sk : SecretKey) (digest : HashOutput) :
    m Signature := do
  let indices := MessageDigest.forsIndices digest
  let address := Scheme.forsAddress digest
  let fors ← Fors.sign indices sk.seed sk.publicKey.seed address
  let forsKey ← Fors.publicKeyFromSignature fors indices sk.publicKey.seed address
  let hypertree ← Hypertree.sign forsKey sk.seed sk.publicKey.seed
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin
  return { randomizer, fors, hypertree }

/-- **The rest of the signer is its digest query and then the rest of the rest.** -/
theorem signInternalAt_eq (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    signInternalAt (m := m) randomizer sk message =
      Hashing.hash (m := m) (Hashing.messageInput randomizer sk.publicKey message) >>=
        fun digest => signInternalRest randomizer sk digest := rfl

/-- **The signer is its two message-dependent queries and then the rest**, as an equality of
computations. The digest query's input is built from the randomiser query's answer, which is
the whole of the ordering. -/
theorem signInternal_eq_two (sk : SecretKey) (message : Bytes) :
    Scheme.signInternal (m := OracleComp HashSpec) sk message =
      Hashing.hash (m := OracleComp HashSpec)
          (Hashing.randomizerInput sk.prf sk.publicKey.seed message) >>= fun answer =>
        Hashing.hash (m := OracleComp HashSpec)
            (Hashing.messageInput (Hashing.truncate answer) sk.publicKey message) >>=
          fun digest => signInternalRest (Hashing.truncate answer) sk digest := by
  rw [signInternal_eq sk message]
  simp only [Hashing.randomizer, Hashing.shortHash, bind_assoc, pure_bind, signInternalAt_eq]

/-! ## What the state says at the second query -/

/-- **The signer's digest query is signer-randomised at the state it is made from.** The
witnesses are the request's own message and the answer the step just produced; nothing is
reconstructed and no entry of the cache is searched for. -/
theorem signerRandomised_digest (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) (step : HashOutput × SplitState)
    (hstep : step ∈ support (((recorder leftKeep rightKeep)
      (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed message))).run state)) :
    SignerRandomised sk.prf sk.publicKey step.2.1
      (Hashing.messageInput (Hashing.truncate step.1) sk.publicKey message) := by
  refine ⟨message, step.1, ?_, rfl⟩
  rw [← recorderOf_cache leftKeep rightKeep] at hstep
  exact recorderOf_step_cache_self leftKeep rightKeep
    (Hashing.randomizerInput sk.prf sk.publicKey.seed message) state step hstep

/-- **So the target test cannot take it.** The two tests are exclusive by priority, and the
disclosing one is exactly `SignerRandomised` at the state in force. -/
theorem not_targetKeep_digest (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (sk : SecretKey) (message : Bytes) (state : SplitState) (step : HashOutput × SplitState)
    (hstep : step ∈ support (((recorder leftKeep rightKeep)
      (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed message))).run state)) :
    ¬ SplitWitness.targetKeep sk.prf sk.publicKey
        (Hashing.messageInput (Hashing.truncate step.1) sk.publicKey message) step.2.1 :=
  fun htarget =>
    htarget.2 (signerRandomised_digest leftKeep rightKeep sk message state step hstep)

end SlhDsaSecurity.SignerDigestStep

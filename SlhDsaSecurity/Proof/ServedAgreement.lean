import SlhDsaSecurity.Proof.ServingPhase
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.SignerRandomiser

/-!
# The carrier's served set and the log's, at a run of the serving phase

`ServingCarrier.AgreesWithLog` is the statement both sides of the composition need to be about
one object: the carrier serves exactly the digest inputs the log names. `ServingPhase` made the
brackets that can make it true — the framing is set across a signing step and clear everywhere
else — and this file is the run-level proof.

**The two directions are proved apart, because they rest on different things.** That the log is
below the carrier rests on what the signer *asks*: its second query is its own digest input, made
while its framing is set, so the handler files it and filing persists. That the carrier is below
the log rests on what the handler *files*: nothing is filed at a clear framing, so every served
input has the shape of some logged request's digest input.

**The signer's two queries are the whole of it.** `sign_shape` cuts `Scheme.sign` at them: the
randomiser's input, then the digest's, whose input carries the randomiser the first answer
truncates to. Everything after is the tail, which this file never looks at.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServedAgreement

open Security OpenCache CanonicalGraph RecordedQueries ServingProgram ServingPhase

variable (publicSeed : Digest)

/-! ## The signer's first two queries -/

/-- **The rest of the signer begins with its digest query.** The tail is whatever follows, and
nothing here looks at it. -/
theorem signInternalAt_shape (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    ∃ rest : HashOutput → OracleComp OracleWorld Signature,
      SignerRandomiser.signInternalAt (m := OracleComp OracleWorld) randomizer sk message =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.messageInput randomizer sk.publicKey message)) :
          OracleComp OracleWorld HashOutput) >>= rest :=
  ⟨_, rfl⟩

open scoped Classical in
/-- **The signer asks its randomiser and then its digest.** The tail is left existential: no
statement here looks past the second query, and naming the tail would mean transcribing
`SignerRandomiser.signInternalAt`'s body. -/
theorem sign_shape (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      Scheme.sign (m := OracleComp OracleWorld) sk request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed := by
  classical
  refine ⟨fun seed digest =>
    (signInternalAt_shape (Hashing.truncate seed) sk framed).choose digest >>=
      fun signature => (pure (some signature.toBytes) : OracleComp OracleWorld (Option Bytes)),
    ?_⟩
  simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, Hashing.randomizer,
    Hashing.shortHash, Hashing.hash, bind_assoc, pure_bind]
  refine congrArg (Bind.bind _) (funext fun seed => ?_)
  have hchoose := (signInternalAt_shape (Hashing.truncate seed) sk framed).choose_spec
  generalize (signInternalAt_shape (Hashing.truncate seed) sk framed).choose = rest at hchoose ⊢
  rw [hchoose, bind_assoc]
  rfl

/-! ## The log is below the carrier

A request the log names was served, and the step that served it ran with its framing set. The
digest query is therefore filed in the step that answers it, and both the filing and the
randomiser's own cache entry persist to the end of the run. -/

/-- **A served request leaves its own digest input filed**, with the randomiser its first answer
truncates to, and leaves that first answer cached. Both are what the end of the run reads. -/
theorem served_of_sign (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) (state : HandlerState)
    (hframing : state.1.framing = some framed) (result : Option Bytes × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state)) :
    ∃ seed : HashOutput,
      result.2.1.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        HandlerCarrier.Served result.2.1
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) := by
  obtain ⟨rest, hshape⟩ := sign_shape sk request framed hframe
  rw [hshape] at hresult
  obtain ⟨seed, mid, hseedCached, hmidFraming, hmidGrows, -, hrest⟩ :=
    servingProgram_query_step publicSeed pk availableAt table
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) _ state result hresult
  obtain ⟨digest, final, -, -, hfinalGrows, hfinalServed, htail⟩ :=
    servingProgram_query_step publicSeed pk availableAt table
      (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) _ mid result hrest
  have hlast := servingProgram_run_persists publicSeed pk availableAt table _ final result htail
  refine ⟨seed, hlast.1 _ _ (hfinalGrows.1 _ _ hseedCached), hlast.2 _ (hfinalServed ?_)⟩
  exact ⟨framed, hmidFraming.trans hframing, Hashing.truncate seed, by rw [hpk]⟩

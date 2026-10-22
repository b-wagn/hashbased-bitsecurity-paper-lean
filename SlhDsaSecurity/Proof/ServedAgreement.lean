import SlhDsaSecurity.Proof.ServingPhase
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.SignerRandomiser
import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.ProbeContainment

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

/-! ## The phase, over any signer

`ServingPhase.servingPhase` fixes its signer at `Scheme.sign sk`. Everything the agreement
proves about it uses the signer in exactly two places — the two queries it makes first, and
which randomiser a query of digest shape can carry — so the phase is taken here over an
arbitrary signer and those two places become hypotheses.

**It is built beside the fixed one, not in its place.** `servingPhaseWith_sign` is the equality,
by `rfl`, so every statement about `ServingPhase.servingPhase` stands and every reader of it is
untouched; the stripped instance is a second instantiation rather than a replacement.

The two hypotheses are what a signer has to supply, and nothing else is asked of it:

* `SignerShape` — it asks its randomiser and then its digest. This is what the filing argument
  chains `ServingProgram.servingProgram_query_step` along.
* `SignerPins` — it is the lift of a hash-only computation in which the only query of a
  framing's digest shape carries the randomiser the cache replays. This is the half that needs
  the walk to be good, and it is where `ServedBridge.sign_messageShape_randomizer` enters.

Both hold of `Scheme.sign sk` and both hold of `StrippedGame.strippedSign` at the walk's table,
which is the whole content of the transport. -/

/-- The serving phase at an arbitrary signer. -/
noncomputable def servingPhaseWith (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (Multiplicative Tally × SigningLog × HandlerState) ProbComp) :=
  PhaseFusion.fuseServing (servingProgram publicSeed pk availableAt table)
    (recordedAdversaryImpl + recordedSigningOracle signer) startServing stopServing

/-- **And at `Scheme.sign` it is the phase that already exists.** -/
theorem servingPhaseWith_sign (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) :
    servingPhaseWith publicSeed pk availableAt table (Scheme.sign sk) =
      ServingPhase.servingPhase publicSeed pk availableAt table sk := rfl

/-- **What the filing argument asks of a signer**: it asks its randomiser and then its digest. -/
def SignerShape (sk : SecretKey)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∀ (request : Message) (framed : Bytes), request.frame = some framed →
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      signer request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed

/-- **What the containment asks of a signer**: it is the lift of a hash-only computation whose
only query of a framing's digest shape carries the randomiser the cache replays. -/
def SignerPins (sk : SecretKey) (warm : QueryCache HashSpec)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∃ hashSigner : Message → OracleComp HashSpec (Option Bytes),
    (∀ request : Message, signer request =
      OracleComp.liftComp (hashSigner request) OracleWorld) ∧
      ∀ (request : Message) (framed : Bytes), request.frame = some framed →
        ∀ later : QueryCache HashSpec,
          (∀ (input : Bytes) (value : HashOutput), warm input = some value →
            later input = some value) →
          ∀ randomizer : Digest,
            CacheReplay.QueriesUnder later (hashSigner request)
                (Hashing.messageInput randomizer sk.publicKey framed) →
              randomizer = HonestProbes.replayRandomizer later sk framed

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
theorem served_of_signer (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) (state : HandlerState)
    (hframing : state.1.framing = some framed) (result : Option Bytes × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (signer request)).run state)) :
    ∃ seed : HashOutput,
      result.2.1.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        HandlerCarrier.Served result.2.1
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) := by
  obtain ⟨rest, hrest⟩ := hshape request framed hframe
  rw [hrest] at hresult
  obtain ⟨seed, mid, hseedCached, hmidFraming, hmidGrows, -, hrest⟩ :=
    servingProgram_query_step publicSeed pk availableAt table
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) _ state result hresult
  obtain ⟨digest, final, -, -, hfinalGrows, hfinalServed, htail⟩ :=
    servingProgram_query_step publicSeed pk availableAt table
      (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) _ mid result hrest
  have hlast := servingProgram_run_persists publicSeed pk availableAt table _ final result htail
  refine ⟨seed, hlast.1 _ _ (hfinalGrows.1 _ _ hseedCached), hlast.2 _ (hfinalServed ?_)⟩
  exact ⟨framed, hmidFraming.trans hframing, Hashing.truncate seed, by rw [hpk]⟩

/-! ## The step, at the phase

Two facts about a step of `ServingPhase.servingPhase`, both read off the two shapes
`ServingPhase.framing_clear_step` already takes the step apart into: the carrier only grows, and
a signing request files its own digest input. Everything run-level below is these two under an
induction. -/

/-- **Dropping a pure tail does not change the state a run leaves.** The signing oracle's own
sub-run is the signer followed by a log append, and the append is pure. -/
theorem state_of_bind_pure {α β : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) (tail : α → β) (state : HandlerState)
    (result : β × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (computation >>= fun value => (pure (tail value) : OracleComp OracleWorld β))).run
      state)) :
    ∃ inner : α × HandlerState, inner ∈ support
      ((simulateQ (servingProgram publicSeed pk availableAt table) computation).run state) ∧
        result = (tail inner.1, inner.2) := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨inner, hinner, hrest⟩ := hresult
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  exact ⟨inner, hinner, hrest⟩

open scoped Classical in
/-- **A step of the phase grows the carrier.** -/
theorem servingPhaseWith_persists (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhaseWith publicSeed pk availableAt table signer) queried).run
      state)) : HandlerCarrier.Grows state.2.2.1 step.2.2.2.1 := by
  classical
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = inner.2 from by rw [hpure]]
    exact servingProgram_run_persists publicSeed pk availableAt table _ state.2.2 inner hinner
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = stopServing inner.2 from by rw [hpure]]
    refine HandlerCarrier.Grows.trans ?_
      (servingProgram_run_persists publicSeed pk availableAt table _
        (startServing request state.2.2) inner hinner)
    cases hframe : request.frame with
    | none =>
      rw [show startServing request state.2.2 = state.2.2 from by rw [startServing, hframe]]
      exact HandlerCarrier.Grows.refl _
    | some framed =>
      rw [show startServing request state.2.2 =
        (HandlerCarrier.setFraming state.2.2.1 framed, state.2.2.2) from by
          rw [startServing, hframe]]
      exact HandlerCarrier.grows_setFraming state.2.2.1 framed

open scoped Classical in
/-- **A step of the phase leaves the framing clear**, at any signer. `ServingPhase`'s own
invariant, with the signer taken as a parameter — neither half of it looks at what the signer
does: the bracket clears the framing whatever the sub-run did, and outside a request the handler
never writes it. -/
theorem framing_clear_step_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (hclear : state.2.2.1.framing = none)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhaseWith publicSeed pk availableAt table signer)
      queried).run state)) : step.2.2.2.1.framing = none := by
  classical
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = inner.2 from by rw [hpure],
      servingProgram_run_framing publicSeed pk availableAt table _ state.2.2 inner hinner]
    exact hclear
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, -, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = stopServing inner.2 from by rw [hpure]]
    exact ServingPhase.framing_stopServing inner.2

/-! ## What the invariant says about the log's own reading

`ServingCarrier.logServed` names the digest input through `HonestProbes.replayRandomizer`, which
reads the randomiser back off the cache. The invariant's cached clause is what makes that
reading the one the signer used. -/

/-- The randomiser a cache replays is the answer it holds. -/
theorem replayRandomizer_of_cached (cache : QueryCache HashSpec) (sk : SecretKey)
    (framed : Bytes) (seed : HashOutput)
    (hcached : cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed) :
    HonestProbes.replayRandomizer cache sk framed = Hashing.truncate seed := by
  rw [HonestProbes.replayRandomizer]
  simp [CacheReplay.replay, hcached]

/-! ## The signature the signer publishes

`ServedBridge.ServedAgree` names a served input by the randomiser in the **published
signature**; the agreement above names it by the randomiser the **cache** replays. They are the
same randomiser, and that they are is log faithfulness — at this presentation, which had no
lemma for it.

It is one lemma rather than a congruence, and the reason is worth seeing: the two readings pass
through different objects. The signature is what the signing oracle returned and the log kept;
the replay is what a later reader computes from a cache entry. Nothing but the run connects
them.

**The pure half is `randomizer_of_signInternalAt`**: the signer's result carries the randomiser
it was given, whatever its queries answered, because the field is filled from the parameter.
Everything else is the first query's answer being cached and persisting, which the query step
already gives. -/

/-- **The signer's result carries the randomiser it was handed.** A fact about the shape of
`signInternalAt`'s return, independent of what anything answered. -/
theorem randomizer_of_signInternalAt {σ : Type} (impl : QueryImpl OracleWorld (StateT σ ProbComp))
    (randomizer : Digest) (sk : SecretKey) (message : Bytes) (state : σ)
    (result : Signature × σ)
    (hresult : result ∈ support ((simulateQ impl
      (SignerRandomiser.signInternalAt (m := OracleComp OracleWorld) randomizer sk message)).run
      state)) : result.1.randomizer = randomizer := by
  rw [SignerRandomiser.signInternalAt] at hresult
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨a, -, b, -, c, -, d, -, h⟩ := hresult
  rw [h]

/-- **What the log's own reading asks of a signer**: it answers with a signature whose
randomiser the final cache replays. -/
def SignerFaithful (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (signer : Message → OracleComp OracleWorld (Option Bytes)) : Prop :=
  ∀ (request : Message) (framed : Bytes), request.frame = some framed →
    ∀ (state : HandlerState) (result : Option Bytes × HandlerState),
      result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        (signer request)).run state) →
      ∃ signature : Signature, result.1 = some signature.toBytes ∧
        signature.randomizer = HonestProbes.replayRandomizer result.2.1.cache sk framed

open scoped Classical in
/-- **And `Scheme.sign` is faithful.** The randomiser it publishes is the one it derived, and
the derivation's answer is in the cache and stays there. -/
theorem signerFaithful_sign (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) : SignerFaithful publicSeed pk availableAt table sk (Scheme.sign sk) := by
  classical
  intro request framed hframe state result hresult
  have hshape : Scheme.sign (m := OracleComp OracleWorld) sk request =
      (query (spec := OracleWorld)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
        OracleComp OracleWorld HashOutput) >>= fun seed =>
          (SignerRandomiser.signInternalAt (m := OracleComp OracleWorld)
              (Hashing.truncate seed) sk framed >>= fun signature =>
            (pure (some signature.toBytes) : OracleComp OracleWorld (Option Bytes))) := by
    simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, Hashing.randomizer,
      Hashing.shortHash, Hashing.hash, bind_assoc, pure_bind]
    rfl
  rw [hshape] at hresult
  obtain ⟨seed, mid, hseedCached, -, -, -, htail⟩ :=
    servingProgram_query_step publicSeed pk availableAt table
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) _ state result hresult
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at htail
  obtain ⟨inner, hinner, hpure⟩ := htail
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  have hgrow := servingProgram_run_persists publicSeed pk availableAt table _ mid inner hinner
  have hcached : result.2.1.cache
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed := by
    rw [show result.2 = inner.2 from by rw [hpure]]
    exact hgrow.1 _ _ hseedCached
  refine ⟨inner.1, by rw [hpure], ?_⟩
  rw [replayRandomizer_of_cached result.2.1.cache sk framed seed hcached]
  exact randomizer_of_signInternalAt (servingProgram publicSeed pk availableAt table)
    (Hashing.truncate seed) sk framed mid inner hinner

/-! ## The log is below the carrier, at a run

The invariant is stated at the log and the carrier together: every logged request that has a
framing has its randomiser's answer in the cache and its digest input in the served set. Both
clauses are needed. The served one is the conclusion; the cached one is what keeps the *input*
from moving as the run goes on, since the input names the randomiser and the randomiser is read
back off the cache. -/

/-- **What a run leaves true of its log and its carrier.** -/
def LogFiled (sk : SecretKey) (log : SigningLog) (carrier : HandlerCarrier.State) : Prop :=
  ∀ entry ∈ log, ∀ framed : Bytes, entry.1.frame = some framed →
    ∃ (seed : HashOutput) (signature : Signature),
      carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        entry.2 = some signature.toBytes ∧
        signature.randomizer = Hashing.truncate seed ∧
        HandlerCarrier.Served carrier
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)

/-- **It survives growth**, both clauses for the same reason: a carrier that grows keeps its
entries and keeps what it serves. -/
theorem LogFiled.mono {sk : SecretKey} {log : SigningLog} {left right : HandlerCarrier.State}
    (hinv : LogFiled sk log left) (hgrow : HandlerCarrier.Grows left right) :
    LogFiled sk log right := by
  intro entry hentry framed hframe
  obtain ⟨seed, signature, hcached, hanswer, hrandomizer, hserved⟩ := hinv entry hentry framed hframe
  exact ⟨seed, signature, hgrow.1 _ _ hcached, hanswer, hrandomizer, hgrow.2 _ hserved⟩

/-- **And it survives a log that only grows.** -/
theorem LogFiled.append {sk : SecretKey} {log : SigningLog} {carrier : HandlerCarrier.State}
    (hinv : LogFiled sk log carrier) (entry : (_ : Message) × Option Bytes)
    (hentry : ∀ framed : Bytes, entry.1.frame = some framed →
      ∃ (seed : HashOutput) (signature : Signature),
        carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
          entry.2 = some signature.toBytes ∧
          signature.randomizer = Hashing.truncate seed ∧
          HandlerCarrier.Served carrier
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
    LogFiled sk (log ++ [entry]) carrier := by
  intro probe hprobe framed hframe
  rcases List.mem_append.mp hprobe with hold | hnew
  · exact hinv probe hold framed hframe
  · obtain rfl := List.mem_singleton.mp hnew
    exact hentry framed hframe

open scoped Classical in
/-- **A step of the phase preserves it.** The adversary's step changes no log and only grows the
carrier; a signing step appends one entry and files exactly that entry's digest input. -/
theorem logFiled_step_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful publicSeed pk availableAt table sk signer)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhaseWith publicSeed pk availableAt table signer) queried).run
      state)) (hinv : LogFiled sk state.2.1 state.2.2.1) :
    LogFiled sk step.2.2.1 step.2.2.2.1 := by
  classical
  have hgrow := servingPhaseWith_persists publicSeed pk availableAt table signer queried state step hstep
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hinner
    obtain ⟨raw, -, hinnerEq⟩ := hinner
    have hlog : step.2.2.1 = state.2.1 := by rw [hpure, ← hinnerEq]
    rw [hlog]
    exact hinv.mono hgrow
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedSigningOracle] at hinner
    obtain ⟨signStep, hsign, hvalue⟩ := state_of_bind_pure publicSeed pk availableAt table
      (signer request) _ (startServing request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun z => z.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun z => HandlerCarrier.clearFraming z.2.1) hvalue
    rw [hlog]
    refine LogFiled.append (hinv.mono hgrow) _ ?_
    intro framed hframe
    obtain ⟨seed, hcached, hserved⟩ := served_of_signer publicSeed pk availableAt table signer sk
      hpk hshape request framed hframe (startServing request state.2.2)
      (by simp only [startServing, hframe]; rfl) signStep hsign
    obtain ⟨signature, hanswer, hrandomizer⟩ := hfaithful request framed hframe
      (startServing request state.2.2) signStep hsign
    rw [hcarrier]
    refine ⟨seed, signature, hcached, hanswer, ?_, hserved⟩
    rw [hrandomizer, replayRandomizer_of_cached signStep.2.1.cache sk framed seed hcached]

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem logFiled_run_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful publicSeed pk availableAt table sk signer) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      LogFiled sk state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
        computation).run state), LogFiled sk z.2.2.1 z.2.2.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hinv z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state hinv z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (logFiled_step_with publicSeed pk availableAt table signer sk hpk hshape hfaithful queried state step hstep hinv) z hrest

/-- **Nothing is logged at the start**, so the invariant holds there for free. -/
theorem logFiled_nil (sk : SecretKey) (carrier : HandlerCarrier.State) :
    LogFiled sk [] carrier := by
  intro entry hentry
  exact absurd hentry (List.not_mem_nil)

/-- **The log is below the carrier.** Half of `ServingCarrier.AgreesWithLog`, and the half the
carrier's own blindness argument needs: a request the log names has had its digest input filed,
so the signer's own reads are available at the carrier. -/
theorem logServed_subset_served (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State) (hinv : LogFiled sk log carrier)
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value)
    (input : Bytes) (hlog : ServingCarrier.logServed sk later log input) :
    HandlerCarrier.Served carrier input := by
  obtain ⟨entry, hentry, framed, hframe, rfl⟩ := hlog
  obtain ⟨seed, -, hcached, -, -, hserved⟩ := hinv entry hentry framed hframe
  rw [replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]
  exact hserved

/-- **At a run**: from a start with nothing logged, the log of the run is below its carrier. -/
theorem logServed_subset_served_run_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful publicSeed pk availableAt table sk signer) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (carrier : HandlerState)
    (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
      computation).run (accumulated, [], carrier))) (input : Bytes)
    (hlog : ServingCarrier.logServed sk z.2.2.2.1.cache z.2.2.1 input) :
    HandlerCarrier.Served z.2.2.2.1 input :=
  logServed_subset_served sk z.2.2.1 z.2.2.2.1
    (logFiled_run_with publicSeed pk availableAt table signer sk hpk hshape hfaithful computation (accumulated, [], carrier)
      (logFiled_nil sk carrier.1) z hz) z.2.2.2.1.cache (fun _ _ hvalue => hvalue) input hlog

/-! ## The carrier is below the log, as far as the handler decides it

The other direction asks what the carrier serves that the log does not, and the handler settles
most of it by itself: it files only where `HandlerCarrier.FilesLeft` holds, and that test reads
the framing, which is set only across a signing step and names that step's own request. So every
served input has the shape of some logged request's digest input — with *some* randomiser.

**That last word is not the handler's to settle**, and this section does not try to.
`ServingCarrier.logServed` names one randomiser, the one the cache replays, and pinning the
filed input to it is a statement about what the signer *asks*: of all the inputs of its
framing's digest shape, it asks only its own digest's. That is
`ServedBridge.sign_messageShape_randomizer`, stated along `CacheReplay.QueriesUnder` — the
replay semantics — while what is filed here is a query of the handler's run. `served_queriesUnder`
below crosses between the two readings, and `servedLog_sign` puts the shape and the crossing
together; what is proved here is the half that needs neither.

Keeping them apart is worth the two lemmas. The shape holds of every run of this handler and
asks nothing of the signer; the randomiser holds only because the signer is the one being run.
A single statement would have hidden which of the two any later change had broken. -/

/-- A framing that names a logged request. -/
def FramingAdmitted (log : SigningLog) (framing : Option Bytes) : Prop :=
  ∀ framed : Bytes, framing = some framed → ∃ entry ∈ log, entry.1.frame = some framed

theorem FramingAdmitted.none (log : SigningLog) : FramingAdmitted log none := by
  intro framed hframed
  exact absurd hframed (by simp)

theorem FramingAdmitted.mono {log : SigningLog} {framing : Option Bytes}
    (hframing : FramingAdmitted log framing) (entry : (_ : Message) × Option Bytes) :
    FramingAdmitted (log ++ [entry]) framing := by
  intro framed hframed
  obtain ⟨probe, hprobe, hframe⟩ := hframing framed hframed
  exact ⟨probe, List.mem_append.mpr (Or.inl hprobe), hframe⟩

/-- An input of some logged request's digest shape. -/
def ShapeAdmitted (pk : PublicKey) (log : SigningLog) (input : Bytes) : Prop :=
  ∃ entry ∈ log, ∃ framed : Bytes, entry.1.frame = some framed ∧
    ∃ randomizer : Digest, input = Hashing.messageInput randomizer pk framed

theorem ShapeAdmitted.mono {pk : PublicKey} {log : SigningLog} {input : Bytes}
    (hshape : ShapeAdmitted pk log input) (entry : (_ : Message) × Option Bytes) :
    ShapeAdmitted pk (log ++ [entry]) input := by
  obtain ⟨probe, hprobe, framed, hframe, randomizer, hinput⟩ := hshape
  exact ⟨probe, List.mem_append.mpr (Or.inl hprobe), framed, hframe, randomizer, hinput⟩

/-- **A run of the handler serves only inputs of an admitted framing's shape.** -/
theorem servedShape_run {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (log : SigningLog) (computation : OracleComp OracleWorld α) (state : HandlerState)
    (result : α × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run state))
    (hframing : FramingAdmitted log state.1.framing)
    (hstart : ∀ input : Bytes, HandlerCarrier.Served state.1 input → ShapeAdmitted pk log input)
    (input : Bytes) (hserved : HandlerCarrier.Served result.2.1 input) :
    ShapeAdmitted pk log input := by
  refine (servingProgram_invariant publicSeed pk availableAt table
    (fun carrier => FramingAdmitted log carrier.framing ∧
      ∀ probe : Bytes, HandlerCarrier.Served carrier probe → ShapeAdmitted pk log probe)
    (fun carrier probe answer hinv => ⟨hinv.1, hinv.2⟩)
    (fun carrier probe hinv hfiles => ⟨hinv.1, fun served hmem => ?_⟩)
    computation state result hresult ⟨hframing, hstart⟩).2 input hserved
  rcases Multiset.mem_cons.mp hmem with rfl | hrest
  · obtain ⟨framed, hframed, randomizer, hinput⟩ := hfiles
    obtain ⟨entry, hentry, hframe⟩ := hinv.1 framed hframed
    exact ⟨entry, hentry, framed, hframe, randomizer, hinput⟩
  · exact hinv.2 served hrest

open scoped Classical in
/-- **A step of the phase preserves it**, with the framing's own invariant carried alongside:
outside a signing step the framing is clear and nothing is filed at all. -/
theorem servedShape_step_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhaseWith publicSeed pk availableAt table signer) queried).run
      state)) (hclear : state.2.2.1.framing = none)
    (hinv : ∀ input : Bytes, HandlerCarrier.Served state.2.2.1 input →
      ShapeAdmitted pk state.2.1 input) :
    ∀ input : Bytes, HandlerCarrier.Served step.2.2.2.1 input →
      ShapeAdmitted pk step.2.2.1 input := by
  classical
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    have hlog : step.2.2.1 = state.2.1 := by
      have hmapped := hinner
      rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hmapped
      obtain ⟨raw, -, hinnerEq⟩ := hmapped
      rw [hpure, ← hinnerEq]
    have hcarrier : step.2.2.2 = inner.2 := by rw [hpure]
    rw [hlog, hcarrier]
    exact servedShape_run publicSeed pk availableAt table state.2.1
      (((recordedAdversaryImpl world).run).run state.2.1) state.2.2 inner hinner
      (by rw [hclear]; exact FramingAdmitted.none _) hinv
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedSigningOracle] at hinner
    obtain ⟨signStep, hsign, hvalue⟩ := state_of_bind_pure publicSeed pk availableAt table
      (signer request) _ (startServing request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun z => z.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun z => HandlerCarrier.clearFraming z.2.1) hvalue
    rw [hlog, hcarrier]
    intro input hserved
    refine servedShape_run publicSeed pk availableAt table
      (state.2.1 ++ [⟨request, signStep.1⟩]) (signer request)
      (startServing request state.2.2) signStep hsign ?_
      (fun probe hprobe => ?_) input hserved
    · cases hframe : request.frame with
      | none =>
        rw [show (startServing request state.2.2).1 = state.2.2.1 from by
          simp only [startServing, hframe], hclear]
        exact FramingAdmitted.none _
      | some framed =>
        rw [show (startServing request state.2.2).1 =
          HandlerCarrier.setFraming state.2.2.1 framed from by
            simp only [startServing, hframe]]
        intro probe hprobe
        exact ⟨⟨request, signStep.1⟩, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)),
          by rw [← Option.some.inj hprobe]; exact hframe⟩
    · refine ShapeAdmitted.mono (hinv probe ?_) _
      cases hframe : request.frame with
      | none =>
        rw [show (startServing request state.2.2) = state.2.2 from by
          simp only [startServing, hframe]] at hprobe
        exact hprobe
      | some framed =>
        rw [show (startServing request state.2.2) =
          (HandlerCarrier.setFraming state.2.2.1 framed, state.2.2.2) from by
            simp only [startServing, hframe]] at hprobe
        exact hprobe

open scoped Classical in
/-- **And therefore a whole run of the phase.** The framing's own invariant rides along, because
the shape step needs it: at an adversary's query the framing is clear and nothing is filed, and
that is what keeps the adversary out of the served set however long it runs. -/
theorem servedShape_phase_run_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      state.2.2.1.framing = none →
      (∀ input : Bytes, HandlerCarrier.Served state.2.2.1 input →
        ShapeAdmitted pk state.2.1 input) →
      ∀ z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
        computation).run state),
        ∀ input : Bytes, HandlerCarrier.Served z.2.2.2.1 input →
          ShapeAdmitted pk z.2.2.1 input := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hclear hinv z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state hclear hinv z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (framing_clear_step_with publicSeed pk availableAt table signer queried state hclear step hstep)
      (servedShape_step_with publicSeed pk availableAt table signer queried state step hstep hclear hinv)
      z hrest

/-- **From a fresh carrier**: a run of the phase serves only inputs of its own log's requests'
digest shape. The adversary contributes nothing to the served set, whatever it asks. -/
theorem servedShape_phase_run_empty_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count))))
    (input : Bytes) (hserved : HandlerCarrier.Served z.2.2.2.1 input) :
    ShapeAdmitted pk z.2.2.1 input :=
  servedShape_phase_run_with publicSeed pk availableAt table signer computation
    (accumulated, [], (HandlerCarrier.empty, probes, count)) rfl
    (fun probe hprobe => absurd hprobe (ServingProgram.not_served_empty probe)) z hz input hserved

/-! ## What the handler files is what the computation consults

The residue of the last section is one word: the filed input names *some* randomiser, and
`ServingCarrier.logServed` names the one the cache replays. Closing it means getting from "the
handler filed this while running the signer" to "the signer consults this", which is the
crossing `ServedBridge.sign_messageShape_randomizer` is stated on the far side of —
`CacheReplay.QueriesUnder`, the replay path, against a run of `Scheme.sign` at a different
instantiation of its monad.

`StrippedGame.sign_lift` does the instantiation: signing in the game's monad is the lift of
signing in the hash-only one. `served_queriesUnder` does the crossing, by the induction
`ProbeContainment.strip_probes_queriesUnder` does for the probe list, at the served set and at
this handler. The two differ in what they have to track — the record grows at every query, the
served set only where the framing admits one — but the step is the same: the run's answer is
cached and persists, so at any later cache the replayed answer is the one the run took, and the
continuations agree.

Read at a later cache, because that is the only cache at which they do agree: the handler draws
its answers and the replay reads them back, so a cache that does not yet hold them replays
something else. -/

/-- **An input a run files is one the computation consults**, read at any cache the run's own
extends. -/
theorem served_queriesUnder {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (computation : OracleComp HashSpec α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        (OracleComp.liftComp computation OracleWorld)).run state) →
      ∀ later : QueryCache HashSpec,
        (∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
          later input = some value) →
        ∀ probe : Bytes, HandlerCarrier.Served z.2.1 probe →
          HandlerCarrier.Served state.1 probe ∨ CacheReplay.QueriesUnder later computation probe
      := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz later _ probe hserved
    rw [OracleComp.liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]] at hserved
    exact Or.inl hserved
  | query_bind input next ih =>
    intro state z hz later hlater probe hserved
    have hz' : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        (liftM (OracleWorld.query (Sum.inr input)) >>=
          fun answer : HashOutput =>
            OracleComp.liftComp (next answer) OracleWorld)).run state) := hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz'
    obtain ⟨step, hstepRun, hrest⟩ := hz'
    have hcached : step.2.1.cache input = some step.1 :=
      servingProgram_hash_cached publicSeed pk availableAt table input state step hstepRun
    have hpersists : HandlerCarrier.Grows step.2.1 z.2.1 :=
      servingProgram_run_persists publicSeed pk availableAt table _ step.2 z hrest
    have hreplay : CacheReplay.replay later input = step.1 := by
      simp [CacheReplay.replay, hlater input step.1 (hpersists.1 input step.1 hcached)]
    rcases ih step.1 step.2 z hrest later hlater probe hserved with hstep | htail
    · rcases servingProgram_hash_served publicSeed pk availableAt table input state step hstepRun
        probe hstep with hbefore | rfl
      · exact Or.inl hbefore
      · exact Or.inr (CacheReplay.QueriesUnder.head _ _)
    · exact Or.inr (CacheReplay.QueriesUnder.tail input probe next (by rw [hreplay]; exact htail))

/-- **An input a run of the signer files is one the signer consults.** The signer is taken as a
lift of a hash-only computation, which is the only thing the crossing needs. -/
theorem served_queriesUnder_lift (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes))
    (hashSigner : Message → OracleComp HashSpec (Option Bytes))
    (hlift : ∀ request : Message,
      signer request = OracleComp.liftComp (hashSigner request) OracleWorld)
    (request : Message) (state : HandlerState) (z : Option Bytes × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (signer request)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      CacheReplay.QueriesUnder later (hashSigner request) probe := by
  rw [hlift] at hz
  exact served_queriesUnder publicSeed pk availableAt table _ state z hz later hlater probe
    hserved

/-! ## The exact containment, at one request

Two readings of a filed input, put together. The carrier says it has the shape of the framing in
flight — that is the filing rule, and it needs no run. The run says the signer consults it — that
is `served_queriesUnder_sign`. Only the second pins the randomiser, and only through
`ServedBridge.sign_messageShape_randomizer`: of all the inputs of its framing's digest shape the
signer asks only its own digest's, the structural ones being separated by `HashSeparation` and
the randomiser's by length.

So the shape alone was never going to be enough, and neither was the run alone: the shape says
*which framing*, the run says *which randomiser*. -/

/-- **A run under a set framing serves nothing but that framing's shape.** -/
theorem servedFramed_run {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (framed : Bytes) (computation : OracleComp OracleWorld α) (state : HandlerState)
    (hframing : state.1.framing = some framed) (result : α × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run state))
    (probe : Bytes) (hserved : HandlerCarrier.Served result.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      ∃ randomizer : Digest, probe = Hashing.messageInput randomizer pk framed := by
  refine (servingProgram_invariant publicSeed pk availableAt table
    (fun carrier => carrier.framing = some framed ∧
      ∀ p : Bytes, HandlerCarrier.Served carrier p →
        HandlerCarrier.Served state.1 p ∨
          ∃ randomizer : Digest, p = Hashing.messageInput randomizer pk framed)
    (fun carrier input answer hinv => ⟨hinv.1, hinv.2⟩)
    (fun carrier input hinv hfiles => ⟨by rw [HandlerCarrier.framing_file]; exact hinv.1,
      fun p hp => ?_⟩)
    computation state result hresult ⟨hframing, fun p hp => Or.inl hp⟩).2 probe hserved
  rcases Multiset.mem_cons.mp hp with rfl | hrest
  · obtain ⟨witness, hwitness, randomizer, hinput⟩ := hfiles
    rw [hinv.1] at hwitness
    rw [← Option.some.inj hwitness] at hinput
    exact Or.inr ⟨randomizer, hinput⟩
  · exact hinv.2 p hrest

/-- **A served request serves exactly its own digest input.** The randomiser is the one the
cache replays, which is what `ServingCarrier.logServed` names it by. The shape says which
framing and the crossing says which randomiser; neither alone would do. -/
theorem servedLog_signer (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (state : HandlerState) (hframing : state.1.framing = some framed)
    (z : Option Bytes × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (signer request)).run state))
    (later : QueryCache HashSpec)
    (hwarm : ∀ (input : Bytes) (value : HashOutput), warm input = some value →
      later input = some value)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      probe = Hashing.messageInput (HonestProbes.replayRandomizer later sk framed)
        sk.publicKey framed := by
  subst hpk
  obtain ⟨hashSigner, hlift, hpin⟩ := hpins
  rcases served_queriesUnder_lift publicSeed sk.publicKey availableAt table signer hashSigner
    hlift request state z hz later hlater probe hserved with hbefore | hquery
  · exact Or.inl hbefore
  rcases servedFramed_run publicSeed sk.publicKey availableAt table framed (signer request) state
    hframing z hz probe hserved with hbefore | ⟨randomizer, rfl⟩
  · exact Or.inl hbefore
  exact Or.inr (congrArg (fun value => Hashing.messageInput value sk.publicKey framed)
    (hpin request framed hframe later hwarm randomizer hquery))

/-! ## The carrier is below the log, at a run

The invariant is quantified over the cache it will be read at, because the cache a run ends with
is not known while the run is going on, and the randomiser the log names is read back off it.
Quantifying instead of fixing is what lets one statement serve every step.

The adversary's step needs nothing but `servedClear_run`: with the framing clear nothing is
filed, so the served set does not move and the invariant is carried across unchanged. That is
the whole of the adversary's contribution to this direction, and it is the property the cache
proxy could not have had. -/

/-- **A run under a clear framing serves nothing new.** -/
theorem servedClear_run {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) (state : HandlerState)
    (hclear : state.1.framing = none) (result : α × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run state))
    (probe : Bytes) (hserved : HandlerCarrier.Served result.2.1 probe) :
    HandlerCarrier.Served state.1 probe :=
  (servingProgram_invariant publicSeed pk availableAt table
    (fun carrier => carrier.framing = none ∧
      ∀ p : Bytes, HandlerCarrier.Served carrier p → HandlerCarrier.Served state.1 p)
    (fun carrier input answer hinv => ⟨hinv.1, hinv.2⟩)
    (fun carrier input hinv hfiles =>
      absurd hfiles (HandlerCarrier.not_filesLeft_of_clear pk carrier hinv.1 input))
    computation state result hresult ⟨hclear, fun p hp => hp⟩).2 probe hserved

/-- **What a run leaves true of its carrier and its log**, read at any cache the carrier's own
extends. -/
def CarrierLogged (sk : SecretKey) (warm : QueryCache HashSpec) (log : SigningLog)
    (carrier : HandlerCarrier.State) : Prop :=
  ∀ later : QueryCache HashSpec,
    (∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value) →
    (∀ (input : Bytes) (value : HashOutput), warm input = some value →
      later input = some value) →
    ∀ input : Bytes, HandlerCarrier.Served carrier input →
      ServingCarrier.logServed sk later log input

theorem logServed_append (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog)
    (entry : (_ : Message) × Option Bytes) (input : Bytes)
    (hlog : ServingCarrier.logServed sk cache log input) :
    ServingCarrier.logServed sk cache (log ++ [entry]) input := by
  obtain ⟨probe, hprobe, framed, hframe, hinput⟩ := hlog
  exact ⟨probe, List.mem_append.mpr (Or.inl hprobe), framed, hframe, hinput⟩

open scoped Classical in
/-- **A step of the phase preserves it.** -/
theorem carrierLogged_step_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhaseWith publicSeed pk availableAt table signer) queried).run
      state)) (hclear : state.2.2.1.framing = none)
    (hinv : CarrierLogged sk warm state.2.1 state.2.2.1) :
    CarrierLogged sk warm step.2.2.1 step.2.2.2.1 := by
  classical
  have hgrow := servingPhaseWith_persists publicSeed pk availableAt table signer queried state step hstep
  rcases queried with world | request
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    have hlog : step.2.2.1 = state.2.1 := by
      have hmapped := hinner
      rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hmapped
      obtain ⟨raw, -, hinnerEq⟩ := hmapped
      rw [hpure, ← hinnerEq]
    have hcarrier : step.2.2.2 = inner.2 := by rw [hpure]
    rw [hlog]
    intro later hlater hwarm input hserved
    refine hinv later (fun probe value hvalue => hlater probe value (hgrow.1 probe value hvalue))
      hwarm input ?_
    rw [hcarrier] at hserved
    exact servedClear_run publicSeed pk availableAt table _ state.2.2 hclear inner hinner input
      hserved
  · have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle signer request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [run_recordedSigningOracle] at hinner
    obtain ⟨signStep, hsign, hvalue⟩ := state_of_bind_pure publicSeed pk availableAt table
      (signer request) _ (startServing request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun y => y.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun y => HandlerCarrier.clearFraming y.2.1) hvalue
    rw [hlog]
    intro later hlater hwarm input hserved
    have hlaterSign : ∀ (probe : Bytes) (value : HashOutput),
        signStep.2.1.cache probe = some value → later probe = some value :=
      fun probe value hvalue => hlater probe value (by rw [hcarrier]; exact hvalue)
    have hservedSign : HandlerCarrier.Served signStep.2.1 input := by
      rw [hcarrier] at hserved
      exact hserved
    have hold : HandlerCarrier.Served (startServing request state.2.2).1 input →
        ServingCarrier.logServed sk later (state.2.1 ++ [⟨request, signStep.1⟩]) input := by
      intro hbefore
      refine logServed_append sk later state.2.1 _ input
        (hinv later (fun probe value hvalue => hlater probe value (hgrow.1 probe value hvalue))
          hwarm input ?_)
      cases hframe : request.frame with
      | none =>
        rw [show startServing request state.2.2 = state.2.2 from by
          simp only [startServing, hframe]] at hbefore
        exact hbefore
      | some framed =>
        rw [show (startServing request state.2.2).1 =
          HandlerCarrier.setFraming state.2.2.1 framed from by
            simp only [startServing, hframe]] at hbefore
        exact hbefore
    cases hframe : request.frame with
    | none =>
      refine hold ?_
      exact servedClear_run publicSeed pk availableAt table
        (signer request) (startServing request state.2.2)
        (by simp only [startServing, hframe]; exact hclear) signStep hsign input hservedSign
    | some framed =>
      rcases servedLog_signer publicSeed pk availableAt table signer sk hpk hshape warm hpins
        request framed hframe
        (startServing request state.2.2) (by simp only [startServing, hframe]; rfl) signStep hsign
        later hwarm hlaterSign input hservedSign with hbefore | hinput
      · exact hold hbefore
      · exact ⟨⟨request, signStep.1⟩,
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), framed, hframe, hinput⟩

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem carrierLogged_run_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      state.2.2.1.framing = none → CarrierLogged sk warm state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
        computation).run state), CarrierLogged sk warm z.2.2.1 z.2.2.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hclear hinv z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hinv
  | query_bind queried next ih =>
    intro state hclear hinv z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (framing_clear_step_with publicSeed pk availableAt table signer queried state hclear step hstep)
      (carrierLogged_step_with publicSeed pk availableAt table signer sk hpk hshape warm hpins queried state step hstep
        hclear hinv) z hrest

/-- **Nothing is served at the start**, so the invariant holds there for free. -/
theorem carrierLogged_empty (sk : SecretKey) (warm : QueryCache HashSpec) (log : SigningLog) :
    CarrierLogged sk warm log HandlerCarrier.empty :=
  fun _ _ _ input hserved => absurd hserved (ServingProgram.not_served_empty input)

/-! ## `ServingCarrier.AgreesWithLog`, at a run

Both directions, at the carrier's own cache. Neither is the mirror of the other: one is about
what the signer asks and the other about what the handler files, and they were proved in
different shapes for that reason. Putting them together is the last line. -/

/-- **A run of the serving phase leaves the carrier and the log naming the same set.** This is
`ServingCarrier.AgreesWithLog`, which is what lets the entries a probe is paired with and the
event `RoutedSplit.InputBad` be instantiated at one object. -/
theorem agreesWithLogAt_run_with (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) (sk : SecretKey)
    (hpk : sk.publicKey = pk) (hshape : SignerShape sk signer)
    (hfaithful : SignerFaithful publicSeed pk availableAt table sk signer)
    (warm : QueryCache HashSpec) (hpins : SignerPins sk warm signer)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table signer)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count))))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.2.2.1.cache input = some value →
      later input = some value)
    (hwarm : ∀ (input : Bytes) (value : HashOutput), warm input = some value →
      later input = some value) (input : Bytes) :
    HandlerCarrier.Served z.2.2.2.1 input ↔
      ServingCarrier.logServed sk later z.2.2.1 input := by
  constructor
  · exact carrierLogged_run_with publicSeed pk availableAt table signer sk hpk hshape warm hpins
      computation (accumulated, [], (HandlerCarrier.empty, probes, count)) rfl
      (carrierLogged_empty sk warm []) z hz later hlater hwarm input
  · exact logServed_subset_served sk z.2.2.1 z.2.2.2.1
      (logFiled_run_with publicSeed pk availableAt table signer sk hpk hshape hfaithful computation
        (accumulated, [], (HandlerCarrier.empty, probes, count)) (logFiled_nil sk _) z hz)
      later hlater input

/-! ## How long the disclosing recording is

The recording the load concentration is capped by is a list of **fresh** queries passing the
left test, and the left test the repair installs is the carrier's served set. So its length is
bounded by the number of *distinct* served inputs, and the agreement above says exactly what
those are: the image of the log under one map, one input per logged request that has a framing.
Hence the recording is no longer than the signing count, and the cap it has to meet is
`signingLimit`, not twice it.

**Freshness is what makes "distinct" the right word**, and it is the only place it is used here:
a recorded query is not cached when it is recorded and is cached forever after, so no input is
recorded twice. Nothing else about the recorder matters to the count.

**The headroom is a factor of five over four and no more.** The concentration holds up to
`5 * 2 ^ 62`; `signingLimit` is `2 ^ 64 = 4 * 2 ^ 62`, which fits, and `2 * signingLimit` is
`2 ^ 65 = 8 * 2 ^ 62`, which does not — and not by a margin that sharpening could recover, since
`2 ^ 65` is past the *mean* of the Poisson the coupling runs through, not merely past the proved
tail. So an extra entry per served request would have to be excluded rather than paid for.

It is excluded, by the filing test as it stands: a request's own `PRF_msg` query is
`Hashing.randomizerInput` at the framing in flight, and
`ServedBridge.randomizerInput_ne_messageInput` says that is never `Hashing.messageInput` at the
same framing — the format identity inserts `PK.root` before the message, so the two differ in
length. `HandlerCarrier.FilesLeft` compares against the framing in flight and nothing else, so
it is false there. -/

/-- The digest input a logged entry serves, when it has a framing. -/
def servedOf (sk : SecretKey) (cache : QueryCache HashSpec)
    (entry : (_ : Message) × Option Bytes) : Option Bytes :=
  (entry.1.frame).map fun framed =>
    Hashing.messageInput (HonestProbes.replayRandomizer cache sk framed) sk.publicKey framed

/-- **The log's served inputs are the image of the log**, which is what bounds how many there
are. -/
theorem mem_map_servedOf (sk : SecretKey) (cache : QueryCache HashSpec) (log : SigningLog)
    (input : Bytes) (hlog : ServingCarrier.logServed sk cache log input) :
    some input ∈ log.map (servedOf sk cache) := by
  obtain ⟨entry, hentry, framed, hframe, hinput⟩ := hlog
  refine List.mem_map.mpr ⟨entry, hentry, ?_⟩
  rw [servedOf, hframe, Option.map_some, hinput]

/-- **A list of distinct served inputs is no longer than the log.** -/
theorem length_le_log_of_served (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (inputs : List Bytes) (hnodup : inputs.Nodup)
    (hserved : ∀ input ∈ inputs, HandlerCarrier.Served carrier input) :
    inputs.length ≤ log.length := by
  have hsub : inputs.map some ⊆ log.map (servedOf sk carrier.cache) := by
    intro value hvalue
    obtain ⟨input, hinput, rfl⟩ := List.mem_map.mp hvalue
    exact mem_map_servedOf sk carrier.cache log input ((hagree input).mp (hserved input hinput))
  have hnodupMap : (inputs.map some).Nodup :=
    hnodup.map (fun _ _ h => Option.some.inj h)
  simpa using (hnodupMap.subperm hsub).length_le

/-- **The disclosing recording is no longer than the signing count.** The recorder's own
freshness guard supplies the distinctness; the agreement supplies everything else. -/
theorem record_length_le_log (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (record : List (Bytes × HashOutput)) (hnodup : (record.map Prod.fst).Nodup)
    (hserved : ∀ entry ∈ record, HandlerCarrier.Served carrier entry.1) :
    record.length ≤ log.length := by
  have hbound := length_le_log_of_served sk log carrier hagree (record.map Prod.fst) hnodup
    (fun input hinput => by
      obtain ⟨entry, hentry, hvalue⟩ := List.mem_map.mp hinput
      rw [← hvalue]
      exact hserved entry hentry)
  simpa using hbound

/-- **And therefore inside the concentration's cap.** `signingLimit` is `4 * 2 ^ 62` and the
concentration holds to `5 * 2 ^ 62`, so the disclosing cap is met with a quarter to spare — and
would be missed, with no way back, at twice the signing limit. -/
theorem record_length_le_cap (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State)
    (hagree : ServingCarrier.AgreesWithLog sk log carrier)
    (record : List (Bytes × HashOutput)) (hnodup : (record.map Prod.fst).Nodup)
    (hserved : ∀ entry ∈ record, HandlerCarrier.Served carrier entry.1)
    (hlimit : log.length ≤ signingLimit) : record.length ≤ 5 * 2 ^ 62 :=
  le_trans (le_trans (record_length_le_log sk log carrier hagree record hnodup hserved) hlimit)
    (by norm_num [signingLimit])

/-- **A served request's own `PRF_msg` query is never filed**, so it never reaches the
disclosing recording and the count stays one per request.

This is the case that could have doubled the cap, and it is closed by length alone: the format
identity reads a message input as a `PRF_msg` input at `PK.root ‖ m`, so a `PRF_msg` input at
`m` itself is one block short of being a message input at `m`. `HandlerCarrier.FilesLeft`
compares against the framing in flight, which is the signer's own `m`, so the two never meet. -/
theorem not_filesLeft_randomizerInput (pk : PublicKey) (sk : SecretKey) (hpk : sk.publicKey = pk)
    (carrier : HandlerCarrier.State) (framed : Bytes)
    (hframing : carrier.framing = some framed) :
    ¬ HandlerCarrier.FilesLeft pk carrier
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) := by
  subst hpk
  rintro ⟨inFlight, hinFlight, randomizer, hinput⟩
  rw [hframing] at hinFlight
  rw [← Option.some.inj hinFlight] at hinput
  exact ServedBridge.randomizerInput_ne_messageInput sk.prf randomizer sk.publicKey framed hinput

/-! ## The same two queries, under stripping

The agreement is proved at a presentation whose signer is unstripped. The input half's
containment is proved at a stripped one, and its honest-phase argument *turns on* stripping:
`StrippedGame.strippedSign` answers canonical probes from the walk's table inside the
computation, so they never reach the handler and the only probes that do are the randomiser's
and the digest's. Moving the containment up to an unstripped signer would mean redoing that
argument against probes that now arrive; moving the agreement down means checking one thing.

**That one thing is here.** Stripping removes a query only where the walk's table answers it,
and the two queries the agreement rests on are not of that kind: a randomiser input and a
message input aim nowhere, so the table is silent at both and they reach the handler exactly as
before. The coldness is taken as a hypothesis, in the shape `ProbeContainment` already threads
it, because that is where the walk's `hpublic` and `hprf` are in hand.

What this says is that the agreement's *proof* transports: the two-query shape it chains
`servingProgram_query_step` along survives stripping unchanged, so `served_of_signer` and
everything above it do too.

**Currently unconsumed, and true.** The composition reads the containment at the *unstripped*
signer, because its blindness step asks for the same computation at two tables and
`StrippedGame.strippedSign` takes the whole table as its warm cache — so two tables differing
anywhere give two different computations and the step could only hold at everything. With
`Scheme.sign` it holds, because that signer reads no cache and depends on the table only through
the key, whose coordinates `RedrawCell.open_seedAndRoot` covers. So the stripped instantiation
below is kept rather than used, and what would consume it is a presentation that strips the
signer against something smaller than the whole table. -/

/-- The signer's two queries at the hash-only monad, which is where stripping acts. -/
theorem signInternalAt_shape_hash (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    ∃ rest : HashOutput → OracleComp HashSpec Signature,
      SignerRandomiser.signInternalAt (m := OracleComp HashSpec) randomizer sk message =
        (query (spec := HashSpec) (Hashing.messageInput randomizer sk.publicKey message) :
          OracleComp HashSpec HashOutput) >>= rest :=
  ⟨_, rfl⟩

open scoped Classical in
/-- **`Scheme.sign` asks its randomiser and then its digest**, at the hash-only monad. -/
theorem sign_shape_hash (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    ∃ rest : HashOutput → HashOutput → OracleComp HashSpec (Option Bytes),
      Scheme.sign (m := OracleComp HashSpec) sk request =
        (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
          OracleComp HashSpec HashOutput) >>= fun seed =>
            (query (spec := HashSpec)
                (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
              OracleComp HashSpec HashOutput) >>= rest seed := by
  classical
  refine ⟨fun seed digest =>
    (signInternalAt_shape_hash (Hashing.truncate seed) sk framed).choose digest >>=
      fun signature => (pure (some signature.toBytes) : OracleComp HashSpec (Option Bytes)),
    ?_⟩
  simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, Hashing.randomizer,
    Hashing.shortHash, Hashing.hash, bind_assoc, pure_bind]
  refine congrArg (Bind.bind _) (funext fun seed => ?_)
  have hchoose := (signInternalAt_shape_hash (Hashing.truncate seed) sk framed).choose_spec
  generalize (signInternalAt_shape_hash (Hashing.truncate seed) sk framed).choose = rest
    at hchoose ⊢
  rw [hchoose, bind_assoc]

open scoped Classical in
/-- **Stripping leaves the signer's two queries in place**, when the walk's table is silent at
them — which on a good walk it is, since neither aims anywhere. So the stripped signer has the
shape `served_of_sign` chains along, and the agreement transports to the stripped run. -/
theorem strippedSign_shape (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (framed : Bytes) (hframe : request.frame = some framed)
    (hrand : warm (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = none)
    (hdigest : ∀ seed : HashOutput,
      warm (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) = none) :
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      StrippedGame.strippedSign warm sk request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed := by
  classical
  obtain ⟨rest, hshape⟩ := sign_shape_hash sk request framed hframe
  refine ⟨fun seed digest =>
    OracleComp.liftComp (simulateQ (StripCached.stripImpl warm) (rest seed digest)) OracleWorld,
    ?_⟩
  rw [StrippedGame.strippedSign, hshape]
  rw [simulateQ_bind,
    show simulateQ (StripCached.stripImpl warm)
        (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
          OracleComp HashSpec HashOutput) =
      (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
        OracleComp HashSpec HashOutput) from by
      simp [StripCached.stripImpl, hrand]]
  rw [OracleComp.liftComp_bind]
  refine congrArg (Bind.bind _) (funext fun seed => ?_)
  rw [simulateQ_bind,
    show simulateQ (StripCached.stripImpl warm)
        (query (spec := HashSpec)
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
          OracleComp HashSpec HashOutput) =
      (query (spec := HashSpec)
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
        OracleComp HashSpec HashOutput) from by
      simp [StripCached.stripImpl, hdigest seed]]
  rw [OracleComp.liftComp_bind]
  rfl

/-! ### And the coldness is the walk's own hypotheses

The two conditions `strippedSign_shape` asks for are not new assumptions. The walk's table is
keyed by canonical inputs, and a canonical input is a tweakable input at a structural address;
the two the signer asks are a randomiser's and a message digest's, and `HashSeparation` keeps
those apart from tweakable inputs under exactly the two coincidences a good walk excludes. So
the hypotheses discharge from `hprf` and `hpublic`, which the containment already carries. -/

/-- **The walk's table is silent at a randomiser input**, the seeds differing. -/
theorem openCache_randomizerInput_eq_none (publicSeed prf seed : Digest) (message : Bytes)
    (hne : prf ≠ publicSeed) (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) :
    OpenCache.openCache publicSeed available table
      (Hashing.randomizerInput prf seed message) = none :=
  OpenCache.openCache_eq_none_of_not_canonical (publicSeed := publicSeed)
    (available := available) table _
    (fun _ => Ne.symm (HashSeparation.randomizer_tweakable_ne hne))

/-- **And at a message-digest input**, the key being no coincidence. -/
theorem openCache_messageInput_eq_none (publicSeed randomizer : Digest) (pk : PublicKey)
    (message : Bytes) (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) :
    OpenCache.openCache publicSeed available table
      (Hashing.messageInput randomizer pk message) = none :=
  OpenCache.openCache_eq_none_of_not_canonical (publicSeed := publicSeed)
    (available := available) table _
    (fun parent => Ne.symm
      (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent)))

/-- **The stripped signer keeps its two queries, on a good walk.** `strippedSign_shape` with
both coldness conditions discharged, which is the statement the transport actually uses. -/
theorem strippedSign_shape_of_good (publicSeed : Digest)
    (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) (sk : SecretKey)
    (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed) :
    ∃ rest : HashOutput → HashOutput → OracleComp OracleWorld (Option Bytes),
      StrippedGame.strippedSign (OpenCache.openCache publicSeed available table) sk request =
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
          OracleComp OracleWorld HashOutput) >>= fun seed =>
            (query (spec := OracleWorld)
                (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
              OracleComp OracleWorld HashOutput) >>= rest seed :=
  strippedSign_shape _ sk request framed hframe
    (openCache_randomizerInput_eq_none publicSeed sk.prf sk.publicKey.seed framed hprf available
      table)
    (fun seed => openCache_messageInput_eq_none publicSeed (Hashing.truncate seed) sk.publicKey
      framed hpublic available table)

/-! ## The two signers

Both instantiations, side by side. `Scheme.sign` needs no table — nothing is stripped, so the
pin holds at every cache — and the stripped signer needs the walk's own table, because the pin
is read through `ProbeContainment.queriesUnder_strip` and that is where the cache has to extend
what stripping answers from.

Nothing here replaces `ServingPhase.servingPhase`: `servingPhaseWith_sign` says the phase at the
first of these *is* that one, so both live and whoever switches does so when their own side is
green. -/

/-- **`Scheme.sign` asks its randomiser and then its digest.** -/
theorem signerShape_sign (sk : SecretKey) : SignerShape sk (Scheme.sign sk) :=
  fun request framed hframe => sign_shape sk request framed hframe

/-- **And its digest query is the only one of its framing's shape**, on a good walk. Nothing is
stripped, so the pin holds at every cache and the table is empty. -/
theorem signerPins_sign (sk : SecretKey)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root)) :
    SignerPins sk (fun _ => none) (Scheme.sign sk) :=
  ⟨fun request => Scheme.sign (m := OracleComp HashSpec) sk request,
    fun request => StrippedGame.sign_lift sk request,
    fun request framed hframe later _ randomizer hquery =>
      ServedBridge.sign_messageShape_randomizer later sk request framed hframe hpublic randomizer
        hquery⟩

/-- **The stripped signer asks the same two queries**, the walk's table being silent at both.

*Currently unconsumed: see the note above the stripping section. Kept because it is the half of
the transport that could have failed, and because what retires it is a change of presentation
rather than a change of fact.* -/
theorem signerShape_strippedSign (publicSeed : Digest)
    (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) (sk : SecretKey)
    (hprf : sk.prf ≠ publicSeed)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root)) :
    SignerShape sk
      (StrippedGame.strippedSign (OpenCache.openCache publicSeed available table) sk) :=
  fun request framed hframe =>
    strippedSign_shape_of_good publicSeed available table sk hprf hpublic request framed hframe

/-- **And the pin survives stripping**, read at a cache extending the table.
`ProbeContainment.queriesUnder_strip` is the step, and the cache condition is exactly its.

*Currently unconsumed, like `signerShape_strippedSign`. Its side condition is not dead weight
even so: it is what made `SignerPins` carry a table at all, and that parameter is now in the
unstripped statement too, where it is vacuous and was previously invisible rather than absent.* -/
theorem signerPins_strippedSign (publicSeed : Digest)
    (available : CanonicalGraph.Node → Prop)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) (sk : SecretKey)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root)) :
    SignerPins sk (OpenCache.openCache publicSeed available table)
      (StrippedGame.strippedSign (OpenCache.openCache publicSeed available table) sk) :=
  ⟨fun request => simulateQ
      (StripCached.stripImpl (OpenCache.openCache publicSeed available table))
      (Scheme.sign (m := OracleComp HashSpec) sk request),
    fun _ => rfl,
    fun request framed hframe later hwarm randomizer hquery =>
      ServedBridge.sign_messageShape_randomizer later sk request framed hframe hpublic randomizer
        (ProbeContainment.queriesUnder_strip _ _ later hwarm _ hquery)⟩

/-! ## The two agreements

The unstripped one keeps its old name and shape, so its readers are untouched; the stripped one
is the same theorem at the other signer, read at a cache extending the walk's table. -/

/-- **A run of the serving phase leaves the carrier and the log naming the same set.** -/
theorem agreesWithLog_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (ServingPhase.servingPhase publicSeed pk availableAt table sk)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count)))) :
    ServingCarrier.AgreesWithLog sk z.2.2.1 z.2.2.2.1 :=
  fun input => agreesWithLogAt_run_with publicSeed pk availableAt table (Scheme.sign sk) sk hpk
    (signerShape_sign sk) (signerFaithful_sign publicSeed pk availableAt table sk)
    (fun _ => none) (signerPins_sign sk hpublic) computation accumulated
    probes count z hz z.2.2.2.1.cache (fun _ _ hvalue => hvalue)
    (fun _ _ hvalue => absurd hvalue (by simp)) input

/-- **The same, at the stripped signer**, read at any cache extending the carrier's and the
walk's table — which is what the game's own `RedrawCell.unionCache` is.

*Currently unconsumed; the composition takes `servedAgree_run` at the unstripped signer instead.
Its faithfulness hypothesis is left as a hypothesis for the same reason: proving it would be
work spent on a statement nothing reads.* -/
theorem agreesWithLogAt_run_stripped (publicSeed' : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (available : CanonicalGraph.Node → Prop) (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hprf : sk.prf ≠ publicSeed')
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (hfaithful : SignerFaithful publicSeed pk availableAt table sk
      (StrippedGame.strippedSign (OpenCache.openCache publicSeed' available table) sk))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhaseWith publicSeed pk availableAt table
        (StrippedGame.strippedSign (OpenCache.openCache publicSeed' available table) sk))
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count))))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.2.2.1.cache input = some value →
      later input = some value)
    (hwarm : ∀ (input : Bytes) (value : HashOutput),
      OpenCache.openCache publicSeed' available table input = some value →
        later input = some value) (input : Bytes) :
    HandlerCarrier.Served z.2.2.2.1 input ↔
      ServingCarrier.logServed sk later z.2.2.1 input :=
  agreesWithLogAt_run_with publicSeed pk availableAt table _ sk hpk
    (signerShape_strippedSign publicSeed' available table sk hprf hpublic) hfaithful
    (OpenCache.openCache publicSeed' available table)
    (signerPins_strippedSign publicSeed' available table sk hpublic) computation accumulated
    probes count z hz later hlater hwarm input

/-! ## Where the agreement cannot be read, and why

`TableTail.handlerRun` is the run the input half's containment is stated at, and it cannot carry
this agreement. Not because of stripping — that transports, as above — but because of the two
things the serving presentation supplies and that one does not.

It runs `OpenCache.lazyProgram`, which caches and does not file, and
`RecordedPhase.unchargedPhase`, which calls its signer through `liftM` with no bracket around
it. So the framing is never set and nothing is ever filed: the carrier's served set is empty at
every reachable state, whatever the adversary and however many requests are served.

`not_served_lazyProgram_run` is that, proved rather than argued, because the consequence is
sharp: `ServedBridge.ServedAgree` at such a run asserts in its `LogBelowCarrier` half that every
logged request's digest input is served, and from an empty carrier that forces the log to serve
nothing. The statement is not merely unproved there; it is false as soon as one framed request
is signed.

The repair is the one this file is built for — `servingPhaseWith` at the stripped signer, which
files and brackets — and it is a change to the *presentation* the containment is read at, not to
the containment. -/

open scoped Classical in
/-- **The plain handler never serves anything.** It caches; only filing adds to the served set,
and this handler does not file. -/
theorem lazyProgram_served (available : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((OpenCache.lazyProgram publicSeed available table) queried).run
      state)) : step.2.1.served = state.1.served := by
  classical
  rcases queried with coin | input
  · rw [OpenCache.lazyProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
  · have hbind : step ∈ support
        (LazyBudget.lazyAnswer publicSeed available table input state.1 >>= fun inner =>
          (pure (inner.1, (inner.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1 = inner.2 from by rw [hpure]]
    exact ServingProgram.lazyAnswer_served publicSeed available table input state.1 inner hinner

/-- **And therefore a whole run of it.** -/
theorem lazyProgram_run_served {α : Type} (available : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed available table)
        computation).run state) → z.2.1.served = state.1.served := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    rw [ih step.1 step.2 z hrest,
      lazyProgram_served publicSeed available table queried state step hstep]

/-- **From an empty carrier, a run of the plain handler serves nothing.** So the two-sided
agreement cannot hold at such a run once a framed request is signed. -/
theorem not_served_lazyProgram_run {α : Type} (available : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (z : α × HandlerState)
    (hz : z ∈ support ((simulateQ (OpenCache.lazyProgram publicSeed available table)
      computation).run (HandlerCarrier.empty, record, count))) (input : Bytes) :
    ¬ HandlerCarrier.Served z.2.1 input := by
  intro hserved
  have hfixed := lazyProgram_run_served publicSeed available table computation
    (HandlerCarrier.empty, record, count) z hz
  refine absurd (show input ∈ HandlerCarrier.empty.served from ?_) (by simp [HandlerCarrier.empty])
  rw [← hfixed]
  exact hserved

/-! ## `ServedBridge.ServedAgree`, which is the shape the join consumes

Everything above names a served input by the randomiser the cache replays. `ServedLog.servedLog`
names it by the randomiser in the **published signature**, and that is the shape the composition
reads, because its consequences — `ServedBridge.disclosedAt_subset_disclosedByLog` and its
converse — are what make the carrier's and the log's disclosure sets one `Finset`.

The two readings meet at `LogFiled`'s own clauses, which is why there is no separate faithfulness
induction: the invariant already carries the signature the log kept and the cache entry the
replay reads, and says they agree. `Signature.fromBytes_toBytes` does the rest, since a parse of
the bytes the signer published is the signature it published. -/

/-- **The log's two readings of a served input are one.** -/
theorem servedLog_iff_logServed (sk : SecretKey) (pk : PublicKey) (hpk : sk.publicKey = pk)
    (log : SigningLog) (carrier : HandlerCarrier.State) (hinv : LogFiled sk log carrier)
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      later input = some value)
    (result : (Outcome × Nat) × QueryCache HashSpec) (hsigned : result.1.1.signed = log)
    (input : Bytes) :
    ServedLog.servedLog pk result input ↔ ServingCarrier.logServed sk later log input := by
  subst hpk
  constructor
  · rintro ⟨entry, hentry, framed, bytes, parsed, hframe, hanswer, hparsed, rfl⟩
    rw [hsigned] at hentry
    obtain ⟨seed, signature, hcached, hsigAnswer, hrandomizer, -⟩ := hinv entry hentry framed hframe
    have hbytes : bytes = signature.toBytes := Option.some.inj (hanswer.symm.trans hsigAnswer)
    have hparse : parsed = signature := by
      rw [hbytes, Signature.fromBytes_toBytes] at hparsed
      exact (Option.some.inj hparsed).symm
    refine ⟨entry, hentry, framed, hframe, ?_⟩
    rw [hparse, hrandomizer,
      replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]
  · rintro ⟨entry, hentry, framed, hframe, rfl⟩
    obtain ⟨seed, signature, hcached, hsigAnswer, hrandomizer, -⟩ := hinv entry hentry framed hframe
    refine ⟨entry, by rw [hsigned]; exact hentry, framed, signature.toBytes, signature, hframe,
      hsigAnswer, Signature.fromBytes_toBytes signature, ?_⟩
    rw [hrandomizer, replayRandomizer_of_cached later sk framed seed (hlater _ seed hcached)]

/-- **The two-sided agreement, at a run of the serving phase.** This is the hypothesis the
composition names: the carrier serves exactly the digest inputs the log does, read at the
game's own cache.

The run's cache and the cache the log is read at are two parameters, because the consumer reads
the log at `RedrawCell.unionCache` — the game's cache, which extends the handler's. Nothing in
`ServedLog.servedLog` reads the result's `Nat`, so a caller pairing the outcome with any count
is the same statement. -/
theorem servedAgree_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (ServingPhase.servingPhase publicSeed pk availableAt table sk)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count))))
    (result : (Outcome × Nat) × QueryCache HashSpec) (hsigned : result.1.1.signed = z.2.2.1)
    (hcache : ∀ (input : Bytes) (value : HashOutput),
      z.2.2.2.1.cache input = some value → result.2 input = some value) :
    ServedBridge.ServedAgree pk z.2.2.2.1 result := by
  have hfiled : LogFiled sk z.2.2.1 z.2.2.2.1 :=
    logFiled_run_with publicSeed pk availableAt table (Scheme.sign sk) sk hpk
      (signerShape_sign sk) (signerFaithful_sign publicSeed pk availableAt table sk) computation
      (accumulated, [], (HandlerCarrier.empty, probes, count)) (logFiled_nil sk _) z hz
  have hiff := servedLog_iff_logServed sk pk hpk z.2.2.1 z.2.2.2.1 hfiled result.2 hcache result
    hsigned
  have hagree := agreesWithLogAt_run_with publicSeed pk availableAt table (Scheme.sign sk) sk hpk
    (signerShape_sign sk) (signerFaithful_sign publicSeed pk availableAt table sk)
    (fun _ => none) (signerPins_sign sk hpublic) computation accumulated probes count z hz
    result.2 hcache (fun _ _ hvalue => absurd hvalue (by simp))
  exact ⟨fun input hserved => (hiff input).mpr ((hagree input).mp hserved),
    fun input hlog => (hagree input).mpr ((hiff input).mp hlog)⟩

end SlhDsaSecurity.ServedAgreement

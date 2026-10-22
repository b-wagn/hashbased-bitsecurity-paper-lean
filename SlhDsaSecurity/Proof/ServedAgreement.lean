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
theorem servingPhase_persists (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhase publicSeed pk availableAt table sk) queried).run
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
          (((recordedSigningOracle (Scheme.sign sk) request).run).run state.2.1)).run
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

/-! ## The log is below the carrier, at a run

The invariant is stated at the log and the carrier together: every logged request that has a
framing has its randomiser's answer in the cache and its digest input in the served set. Both
clauses are needed. The served one is the conclusion; the cached one is what keeps the *input*
from moving as the run goes on, since the input names the randomiser and the randomiser is read
back off the cache. -/

/-- **What a run leaves true of its log and its carrier.** -/
def LogFiled (sk : SecretKey) (log : SigningLog) (carrier : HandlerCarrier.State) : Prop :=
  ∀ entry ∈ log, ∀ framed : Bytes, entry.1.frame = some framed →
    ∃ seed : HashOutput,
      carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
        HandlerCarrier.Served carrier
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)

/-- **It survives growth**, both clauses for the same reason: a carrier that grows keeps its
entries and keeps what it serves. -/
theorem LogFiled.mono {sk : SecretKey} {log : SigningLog} {left right : HandlerCarrier.State}
    (hinv : LogFiled sk log left) (hgrow : HandlerCarrier.Grows left right) :
    LogFiled sk log right := by
  intro entry hentry framed hframe
  obtain ⟨seed, hcached, hserved⟩ := hinv entry hentry framed hframe
  exact ⟨seed, hgrow.1 _ _ hcached, hgrow.2 _ hserved⟩

/-- **And it survives a log that only grows.** -/
theorem LogFiled.append {sk : SecretKey} {log : SigningLog} {carrier : HandlerCarrier.State}
    (hinv : LogFiled sk log carrier) (entry : (_ : Message) × Option Bytes)
    (hentry : ∀ framed : Bytes, entry.1.frame = some framed →
      ∃ seed : HashOutput,
        carrier.cache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some seed ∧
          HandlerCarrier.Served carrier
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
    LogFiled sk (log ++ [entry]) carrier := by
  intro probe hprobe framed hframe
  rcases List.mem_append.mp hprobe with hold | hnew
  · exact hinv probe hold framed hframe
  · rw [List.mem_singleton.mp hnew] at hframe
    exact hentry framed hframe

open scoped Classical in
/-- **A step of the phase preserves it.** The adversary's step changes no log and only grows the
carrier; a signing step appends one entry and files exactly that entry's digest input. -/
theorem logFiled_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhase publicSeed pk availableAt table sk) queried).run
      state)) (hinv : LogFiled sk state.2.1 state.2.2.1) :
    LogFiled sk step.2.2.1 step.2.2.2.1 := by
  classical
  have hgrow := servingPhase_persists publicSeed pk availableAt table sk queried state step hstep
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
          (((recordedSigningOracle (Scheme.sign sk) request).run).run state.2.1)).run
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
      (Scheme.sign sk request) _ (startServing request state.2.2) inner hinner
    have hlog : step.2.2.1 = state.2.1 ++ [⟨request, signStep.1⟩] := by
      rw [hpure]
      exact congrArg (fun z => z.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun z => HandlerCarrier.clearFraming z.2.1) hvalue
    rw [hlog]
    refine LogFiled.append (hinv.mono hgrow) _ ?_
    intro framed hframe
    obtain ⟨seed, hcached, hserved⟩ := served_of_sign publicSeed pk availableAt table sk hpk
      request framed hframe (startServing request state.2.2)
      (by simp only [startServing, hframe]; rfl) signStep hsign
    rw [hcarrier]
    exact ⟨seed, hcached, hserved⟩

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem logFiled_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      LogFiled sk state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
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
      (logFiled_step publicSeed pk availableAt table sk hpk queried state step hstep hinv) z hrest

/-- **Nothing is logged at the start**, so the invariant holds there for free. -/
theorem logFiled_nil (sk : SecretKey) (carrier : HandlerCarrier.State) :
    LogFiled sk [] carrier := by
  intro entry hentry
  exact absurd hentry (List.not_mem_nil)

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

/-- **The log is below the carrier.** Half of `ServingCarrier.AgreesWithLog`, and the half the
carrier's own blindness argument needs: a request the log names has had its digest input filed,
so the signer's own reads are available at the carrier. -/
theorem logServed_subset_served (sk : SecretKey) (log : SigningLog)
    (carrier : HandlerCarrier.State) (hinv : LogFiled sk log carrier) (input : Bytes)
    (hlog : ServingCarrier.logServed sk carrier.cache log input) :
    HandlerCarrier.Served carrier input := by
  obtain ⟨entry, hentry, framed, hframe, rfl⟩ := hlog
  obtain ⟨seed, hcached, hserved⟩ := hinv entry hentry framed hframe
  rw [replayRandomizer_of_cached carrier.cache sk framed seed hcached]
  exact hserved

/-- **At a run**: from a start with nothing logged, the log of the run is below its carrier. -/
theorem logServed_subset_served_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (carrier : HandlerState)
    (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
      computation).run (accumulated, [], carrier))) (input : Bytes)
    (hlog : ServingCarrier.logServed sk z.2.2.2.1.cache z.2.2.1 input) :
    HandlerCarrier.Served z.2.2.2.1 input :=
  logServed_subset_served sk z.2.2.1 z.2.2.2.1
    (logFiled_run publicSeed pk availableAt table sk hpk computation (accumulated, [], carrier)
      (logFiled_nil sk carrier.1) z hz) input hlog

end SlhDsaSecurity.ServedAgreement

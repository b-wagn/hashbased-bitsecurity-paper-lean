import SlhDsaSecurity.Proof.ServingPhase
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.SignerRandomiser
import SlhDsaSecurity.Proof.StrippedGame

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
theorem servedShape_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhase publicSeed pk availableAt table sk) queried).run
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
    rw [hlog, hcarrier]
    intro input hserved
    refine servedShape_run publicSeed pk availableAt table
      (state.2.1 ++ [⟨request, signStep.1⟩]) (Scheme.sign sk request)
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
theorem servedShape_phase_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      state.2.2.1.framing = none →
      (∀ input : Bytes, HandlerCarrier.Served state.2.2.1 input →
        ShapeAdmitted pk state.2.1 input) →
      ∀ z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
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
      (framing_clear_step publicSeed pk availableAt table sk queried state hclear step hstep)
      (servedShape_step publicSeed pk availableAt table sk queried state step hstep hclear hinv)
      z hrest

/-- **From a fresh carrier**: a run of the phase serves only inputs of its own log's requests'
digest shape. The adversary contributes nothing to the served set, whatever it asks. -/
theorem servedShape_phase_run_empty (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count))))
    (input : Bytes) (hserved : HandlerCarrier.Served z.2.2.2.1 input) :
    ShapeAdmitted pk z.2.2.1 input :=
  servedShape_phase_run publicSeed pk availableAt table sk computation
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

/-- **An input a run of the signer files is one the signer consults.** `StrippedGame.sign_lift`
is the only thing between this and the lemma above. -/
theorem served_queriesUnder_sign (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (request : Message) (state : HandlerState)
    (z : Option Bytes × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      CacheReplay.QueriesUnder later (Scheme.sign (m := OracleComp HashSpec) sk request) probe := by
  rw [StrippedGame.sign_lift] at hz
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
cache replays, which is what `ServingCarrier.logServed` names it by. -/
theorem servedLog_sign (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (state : HandlerState) (hframing : state.1.framing = some framed)
    (z : Option Bytes × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      (Scheme.sign (m := OracleComp OracleWorld) sk request)).run state))
    (later : QueryCache HashSpec)
    (hlater : ∀ (input : Bytes) (value : HashOutput), z.2.1.cache input = some value →
      later input = some value)
    (probe : Bytes) (hserved : HandlerCarrier.Served z.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨
      probe = Hashing.messageInput (HonestProbes.replayRandomizer later sk framed)
        sk.publicKey framed := by
  subst hpk
  rcases served_queriesUnder_sign publicSeed sk.publicKey availableAt table sk request state z hz
    later hlater probe hserved with hbefore | hquery
  · exact Or.inl hbefore
  rcases servedFramed_run publicSeed sk.publicKey availableAt table framed
    (Scheme.sign (m := OracleComp OracleWorld) sk request) state hframing z hz probe hserved with
    hbefore | ⟨randomizer, rfl⟩
  · exact Or.inl hbefore
  exact Or.inr (congrArg (fun value => Hashing.messageInput value sk.publicKey framed)
    (ServedBridge.sign_messageShape_randomizer later sk request framed hframe hpublic randomizer
      hquery))

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
def CarrierLogged (sk : SecretKey) (log : SigningLog) (carrier : HandlerCarrier.State) : Prop :=
  ∀ later : QueryCache HashSpec,
    (∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
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
theorem carrierLogged_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhase publicSeed pk availableAt table sk) queried).run
      state)) (hclear : state.2.2.1.framing = none)
    (hinv : CarrierLogged sk state.2.1 state.2.2.1) :
    CarrierLogged sk step.2.2.1 step.2.2.2.1 := by
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
    have hlog : step.2.2.1 = state.2.1 := by
      have hmapped := hinner
      rw [run_recordedAdversaryImpl, simulateQ_map, StateT.run_map, support_map] at hmapped
      obtain ⟨raw, -, hinnerEq⟩ := hmapped
      rw [hpure, ← hinnerEq]
    have hcarrier : step.2.2.2 = inner.2 := by rw [hpure]
    rw [hlog]
    intro later hlater input hserved
    refine hinv later (fun probe value hvalue => hlater probe value (hgrow.1 probe value hvalue))
      input ?_
    rw [hcarrier] at hserved
    exact servedClear_run publicSeed pk availableAt table _ state.2.2 hclear inner hinner input
      hserved
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
      exact congrArg (fun y => y.1.2) hvalue
    have hcarrier : step.2.2.2.1 = HandlerCarrier.clearFraming signStep.2.1 := by
      rw [hpure]
      exact congrArg (fun y => HandlerCarrier.clearFraming y.2.1) hvalue
    rw [hlog]
    intro later hlater input hserved
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
          input ?_)
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
        (Scheme.sign (m := OracleComp OracleWorld) sk request) (startServing request state.2.2)
        (by simp only [startServing, hframe]; exact hclear) signStep hsign input hservedSign
    | some framed =>
      rcases servedLog_sign publicSeed pk availableAt table sk hpk hpublic request framed hframe
        (startServing request state.2.2) (by simp only [startServing, hframe]; rfl) signStep hsign
        later hlaterSign input hservedSign with hbefore | hinput
      · exact hold hbefore
      · exact ⟨⟨request, signStep.1⟩,
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), framed, hframe, hinput⟩

open scoped Classical in
/-- **And therefore a whole run of the phase.** -/
theorem carrierLogged_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      state.2.2.1.framing = none → CarrierLogged sk state.2.1 state.2.2.1 →
      ∀ z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
        computation).run state), CarrierLogged sk z.2.2.1 z.2.2.2.1 := by
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
      (framing_clear_step publicSeed pk availableAt table sk queried state hclear step hstep)
      (carrierLogged_step publicSeed pk availableAt table sk hpk hpublic queried state step hstep
        hclear hinv) z hrest

/-- **Nothing is served at the start**, so the invariant holds there for free. -/
theorem carrierLogged_empty (sk : SecretKey) (log : SigningLog) :
    CarrierLogged sk log HandlerCarrier.empty :=
  fun _ _ input hserved => absurd hserved (ServingProgram.not_served_empty input)

/-! ## `ServingCarrier.AgreesWithLog`, at a run

Both directions, at the carrier's own cache. Neither is the mirror of the other: one is about
what the signer asks and the other about what the handler files, and they were proved in
different shapes for that reason. Putting them together is the last line. -/

/-- **A run of the serving phase leaves the carrier and the log naming the same set.** This is
`ServingCarrier.AgreesWithLog`, which is what lets the entries a probe is paired with and the
event `RoutedSplit.InputBad` be instantiated at one object. -/
theorem agreesWithLog_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (hpk : sk.publicKey = pk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (probes : List (Bytes × HandlerCarrier.State))
    (count : Nat) (z : α × (Multiplicative Tally × SigningLog × HandlerState))
    (hz : z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
      computation).run (accumulated, [], (HandlerCarrier.empty, probes, count)))) :
    ServingCarrier.AgreesWithLog sk z.2.2.1 z.2.2.2.1 := by
  intro input
  constructor
  · exact carrierLogged_run publicSeed pk availableAt table sk hpk hpublic computation
      (accumulated, [], (HandlerCarrier.empty, probes, count)) rfl
      (carrierLogged_empty sk []) z hz z.2.2.2.1.cache (fun _ _ hvalue => hvalue) input
  · exact logServed_subset_served sk z.2.2.1 z.2.2.2.1
      (logFiled_run publicSeed pk availableAt table sk hpk computation
        (accumulated, [], (HandlerCarrier.empty, probes, count)) (logFiled_nil sk _) z hz) input

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

end SlhDsaSecurity.ServedAgreement

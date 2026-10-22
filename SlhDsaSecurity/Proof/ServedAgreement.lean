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

/-! ## The carrier is below the log, as far as the handler decides it

The other direction asks what the carrier serves that the log does not, and the handler settles
most of it by itself: it files only where `HandlerCarrier.FilesLeft` holds, and that test reads
the framing, which is set only across a signing step and names that step's own request. So every
served input has the shape of some logged request's digest input — with *some* randomiser.

**That last word is the whole of the remaining gap, and it is not the handler's to close.**
`ServingCarrier.logServed` names one randomiser, the one the cache replays, and pinning the
filed input to it is a statement about what the signer *asks*: of all the inputs of its
framing's digest shape, it asks only its own digest's. That is
`ServedBridge.sign_messageShape_randomizer`, which is stated along `CacheReplay.QueriesUnder` —
the replay semantics — while what is filed here is a query of the handler's run. The bridge
between those two readings of "the signer asked this" is what is missing, and it is a statement
about `Scheme.sign`, not about the carrier.

So this section proves the containment at the shape and names the residue rather than assuming
it. -/

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

end SlhDsaSecurity.ServedAgreement

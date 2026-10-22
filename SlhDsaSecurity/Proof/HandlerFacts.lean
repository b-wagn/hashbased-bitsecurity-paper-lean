import SlhDsaSecurity.Proof.ServingProgram
import SlhDsaSecurity.Proof.ChargedProbe

/-!
# What the stalled stack asks of a handler

`RedrawCell`'s charge — the stall, the redraw, the per-cell weight — is written at
`OpenCache.lazyProgram`. It reads four things about that handler and nothing else:

* it **never fails**;
* a step **grows the carrier**;
* a step **appends one probe** to the record, or none for a coin;
* and a step at a state where a cell is unavailable **does not depend on that cell**.

`ServingProgram.servingProgram` is `lazyProgram` with one addition: a query the in-flight framing
recognises is filed in the same step that caches its answer. The test reads the carrier's framing
and the input, and **never the table** — which is exactly the part of a handler the charge looks
at. So the two handlers differ by nothing the stack reads, and the stack can be stated against
the four facts instead of against one handler.

`Facts` is that interface and this file proves both handlers satisfy it. The charge itself still
names `lazyProgram`; the parameterised copy of the stack is built on top of this and the existing
statements stay as they are until they can be retired as instances. Keeping the copy separate is
deliberate: a parameterisation landing as a replacement would make a merge hazard of every file
that reads the charge, for as long as the work takes.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HandlerFacts

open Security CanonicalGraph OpenCache ChargedProbe

/-- What a step appends to the record: one probe for a hash call, nothing for a coin. -/
def appended (queried : OracleWorld.Domain) (carrier : HandlerCarrier.State) :
    List (Bytes × HandlerCarrier.State) :=
  match queried with
  | Sum.inl _ => []
  | Sum.inr input => [(input, carrier)]

/-- **The four facts the stalled stack reads about a handler.**

**Why `blind` is guarded by `allowed`.** The first three are facts about the handler at one
table. `blind` is not: it compares the handler at *two* tables, so it is a relation between the
handler and the **table family** it ranges over, and a handler may read the table in ways that
make it false at particular cells. The one in this development does. A handler that files what
the signer discloses tests a query against the public key, and `HandlerCarrier.FilesLeft`
unfolds to `Hashing.messageInput randomizer pk framed`, which is
`… ++ bytesBE n pk.seed ++ bytesBE n pk.root ++ message`: the test reads `pk.root`, and at a
drawn table the root **is** a cell, `table.1 (.structural topRoot)`. Two tables differing only
there give that handler two different filing tests, so it is not blind at that index and never
will be.

This is `Lenient`'s reason arriving one level down. `Lenient` could not be a field because it is
about two handlers; `blind` can be a field only because `allowed` says which indices the
comparison is claimed at. **So `allowed` is not a formality and must not be widened back to
`fun _ => True` to make an instance typecheck** — doing so is claiming blindness the handler
does not have. What makes the guard free is that the charge never uses `blind` anywhere else:
every use is at an index it has already shown untouched, and the untouched set already excludes
the root, which `RedrawCell.open_seedAndRoot` pays for. The demand lives at the consumer, as
`∀ index, ¬ touched index → allowed index`. -/
structure Facts (publicSeed : Digest) (availableAt : HandlerCarrier.State → Node → Prop)
    (allowed : Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp)) : Prop where
  /-- The handler never fails. -/
  neverFails : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain)
    (state : HandlerState), Pr[⊥ | ((impl table) queried).run state] = 0
  /-- A step grows the carrier. -/
  grows : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState),
    step ∈ support (((impl table) queried).run state) →
      HandlerCarrier.Grows state.1 step.2.1
  /-- A step appends one probe, or none. -/
  record : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState),
    step ∈ support (((impl table) queried).run state) →
      step.2.2.1 = state.2.1 ++ appended queried state.1
  /-- A step at a state where a cell is unavailable does not read that cell — at the indices
  `allowed` admits, and no others. -/
  blind : ∀ (index : Node), allowed index → ∀ (left right : Cells × Padding),
    AgreeOff index left right →
    ∀ (queried : OracleWorld.Domain) (state : HandlerState), ¬ availableAt state.1 index →
      ((impl left) queried).run state = ((impl right) queried).run state

/-! ## The handler the charge is written at -/

open scoped Classical in
/-- **The lazy handler satisfies the four.** -/
theorem facts_lazyProgram (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop)
    (hclosed : ∀ (carrier : HandlerCarrier.State) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt carrier child) →
        availableAt carrier (.structural parent)) :
    Facts publicSeed availableAt (fun _ => True)
      (fun table => lazyProgram publicSeed availableAt table) where
  neverFails table queried state :=
    lazyProgram_neverFails publicSeed availableAt table queried state
  grows table queried state step hstep :=
    CacheAvailability.lazyProgram_persists publicSeed availableAt table queried state step hstep
  record table queried state step hstep := by
    rcases queried with coin | input
    · rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2 = state from by rw [hpure], appended, List.append_nil]
    · exact (lazyProgram_step_inr publicSeed availableAt table input state step hstep).trans rfl
  blind index _ left right hagree queried state hindex :=
    lazyProgram_step_congr publicSeed availableAt hclosed index left right hagree queried state
      hindex

/-! ## The handler that files

The filing is a function of the carrier's framing and the input, so it is the same on both
tables; everything else is `lazyAnswer`, which the lazy handler's own facts are about. -/


open scoped Classical in
/-- **One answer never fails.** -/
theorem lazyAnswer_neverFails (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (carrier : HandlerCarrier.State) :
    Pr[⊥ | LazyBudget.lazyAnswer publicSeed availableAt table input carrier] = 0 := by
  classical
  rw [LazyBudget.lazyAnswer]
  cases hcached : carrier.cache input with
  | some cached => simp
  | none =>
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer => simp
    | none => simp

open scoped Classical in
/-- **One answer does not read an unavailable cell.** -/
theorem lazyAnswer_congr (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop)
    (hclosed : ∀ (carrier : HandlerCarrier.State) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt carrier child) →
        availableAt carrier (.structural parent))
    (index : Node) (left right : Cells × Padding) (hagree : AgreeOff index left right)
    (input : Bytes) (carrier : HandlerCarrier.State) (hindex : ¬ availableAt carrier index) :
    LazyBudget.lazyAnswer publicSeed availableAt left input carrier =
      LazyBudget.lazyAnswer publicSeed availableAt right input carrier := by
  classical
  rw [LazyBudget.lazyAnswer, LazyBudget.lazyAnswer,
    openCache_congr_of_agreeOff publicSeed (availableAt carrier) (hclosed carrier) index hindex
      left right hagree]

open scoped Classical in
/-- **The serving handler satisfies them too.** -/
theorem facts_servingProgram (publicSeed : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop)
    (hclosed : ∀ (carrier : HandlerCarrier.State) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt carrier child) →
        availableAt carrier (.structural parent)) :
    Facts publicSeed availableAt (fun _ => True)
      (fun table => ServingProgram.servingProgram publicSeed pk availableAt table) where
  neverFails table queried state := by
    classical
    rcases queried with coin | input
    · rw [ServingProgram.servingProgram_run_inl]
      simp
    · have hbind : Pr[⊥ | ((ServingProgram.servingProgram publicSeed pk availableAt table)
          (Sum.inr input)).run state] =
        Pr[⊥ | LazyBudget.lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
          (pure (step.1,
            ((if HandlerCarrier.FilesLeft pk state.1 input then
                HandlerCarrier.file step.2 input else step.2),
              state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))] := rfl
      rw [hbind, probFailure_bind_eq_add_tsum, lazyAnswer_neverFails publicSeed availableAt
        table input state.1]
      simp
  grows table queried state step hstep :=
    ServingProgram.servingProgram_persists publicSeed pk availableAt table queried state step
      hstep
  record table queried state step hstep := by
    classical
    rcases queried with coin | input
    · rw [ServingProgram.servingProgram_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2 = state from by rw [hpure], appended, List.append_nil]
    · have hbind : step ∈ support
          (LazyBudget.lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
            (pure (inner.1,
              ((if HandlerCarrier.FilesLeft pk state.1 input then
                  HandlerCarrier.file inner.2 input else inner.2),
                state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
              ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
      rw [mem_support_bind_iff] at hbind
      obtain ⟨inner, -, hpure⟩ := hbind
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.1 = state.2.1 ++ [(input, state.1)] from by rw [hpure], appended]
  blind index _ left right hagree queried state hindex := by
    classical
    rcases queried with coin | input
    · rw [ServingProgram.servingProgram_run_inl, ServingProgram.servingProgram_run_inl]
    · rw [ServingProgram.servingProgram_run_inr, ServingProgram.servingProgram_run_inr,
        lazyAnswer_congr publicSeed availableAt hclosed index left right hagree input state.1
          hindex]

/-! ## The fifth fact, for the comparison rather than the charge

The charge is proved at the handler run at the *real* availability; the game's own run is the
handler at **total** availability, which answers every canonical input. `ChargedProbe`'s
comparison closes that gap by flagging the queries where the two can differ, and what it asks is
one fact more — that off those queries the two handlers take the same step.

It is a fact about a **pair** of handlers rather than about one, so it cannot be a field of
`Facts`, which is parameterised by a single availability. It is `Lenient`, and both handlers
satisfy it for the same reason: the step at a hash query is `lazyAnswer`'s, and `lazyAnswer`
reads availability only through `openCache`. -/

open scoped Classical in
/-- **One answer, at two availabilities.** -/
theorem lazyAnswer_congr_available (publicSeed : Digest)
    (lenient strict : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (carrier : HandlerCarrier.State)
    (hnot : ∀ parent : StructuralNode, canonicalInput publicSeed table.1 parent = input →
      ((∀ child ∈ parent.children, lenient carrier child) ↔
        ∀ child ∈ parent.children, strict carrier child)) :
    LazyBudget.lazyAnswer publicSeed lenient table input carrier =
      LazyBudget.lazyAnswer publicSeed strict table input carrier := by
  classical
  rw [LazyBudget.lazyAnswer, LazyBudget.lazyAnswer,
    openCache_congr_of_not_sensitive publicSeed (lenient carrier) (strict carrier) table input
      hnot]

/-- **Off the sensitive inputs the two availabilities give the same step.**

Not a field of `Facts`, and not for want of room: an interface collects what **one** object
owes, and this is a relation between two. Making it a field would force a handler to know about
its own alternative — it would have to carry, as part of being a handler, the identity of the
lenient twin it is to be compared against. So it stands beside `Facts`, and a reader needing
both says so by taking both. -/
structure Lenient (publicSeed : Digest) (availableAt : HandlerCarrier.State → Node → Prop)
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp)) : Prop where
  /-- A query that is at no sensitive node's canonical input is answered alike. -/
  agree : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState),
    ¬ ChargedProbe.SensitiveQueryAt publicSeed availableAt table.1 state queried →
      ((lenientImpl table) queried).run state = ((strictImpl table) queried).run state

open scoped Classical in
/-- **The lazy handler at total availability against itself at the real one.** -/
theorem lenient_lazyProgram (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) :
    Lenient publicSeed availableAt (fun table => lazyProgram publicSeed (fun _ _ => True) table)
      (fun table => lazyProgram publicSeed availableAt table) where
  agree table queried state hnot := by
    classical
    rcases queried with coin | input
    · rw [lazyProgram_run_inl, lazyProgram_run_inl]
    · rw [lazyProgram_run_inr, lazyProgram_run_inr,
        openCache_congr_of_not_sensitive publicSeed (fun _ => True) (availableAt state.1) table
          input ?_]
      intro parent hparent
      refine ⟨fun _ child hchild => ?_, fun _ _ _ => trivial⟩
      by_contra hunavailable
      exact hnot ⟨input, rfl, parent, ⟨child, hchild, hunavailable⟩, hparent⟩

open scoped Classical in
/-- **The serving handler at total availability against itself at the real one.** The filing is
the same on both sides, reading the framing and the input and never availability. -/
theorem lenient_servingProgram (publicSeed : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) :
    Lenient publicSeed availableAt
      (fun table => ServingProgram.servingProgram publicSeed pk (fun _ _ => True) table)
      (fun table => ServingProgram.servingProgram publicSeed pk availableAt table) where
  agree table queried state hnot := by
    classical
    rcases queried with coin | input
    · rw [ServingProgram.servingProgram_run_inl, ServingProgram.servingProgram_run_inl]
    · rw [ServingProgram.servingProgram_run_inr, ServingProgram.servingProgram_run_inr,
        lazyAnswer_congr_available publicSeed (fun _ _ => True) availableAt table input state.1
          ?_]
      intro parent hparent
      refine ⟨fun _ child hchild => ?_, fun _ _ _ => trivial⟩
      by_contra hunavailable
      exact hnot ⟨input, rfl, parent, ⟨child, hchild, hunavailable⟩, hparent⟩

/-! ## The availability the charge actually has

`Facts` fixes one availability across the whole statement. The charge **draws the table inside
itself**, and the availability the chain reads is a function of that table: the honest reveal
count is `GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed`. So a statement that
fixes it is stating against something it does not have, and the honest variant of the charge
cannot be instantiated at all.

`TableFacts` is the same interface with the availability indexed by the table, which is the
honest statement. `Facts` is the case of it at a constant availability — `tableFacts_of_facts` —
so nothing that already reads `Facts` has to move, and a reader outside the charge cluster never
notices.

**One field is new, and it is forced by the stall rather than by taste.**
`StalledRun.evalDist_stalled_congr` takes a *single* `Frozen` predicate and compares the handler
at two tables against it. With a table-indexed availability the two sides would stall at
different moments — `availableAt left` on one and `availableAt right` on the other — and the
comparison would not be between stalled runs of the same shape at all. `availBlind` is what
rules that out: at an index the comparison is allowed at, the availability itself does not read
the cells that distinguish the two tables. It is `blind` one layer down, with the same guard and
for the same reason, and at the chain's availability it is closed by the same fact — that
`seedAndRoot` names the seed, so tables agreeing off an untouched index agree at it. -/

/-- **The four facts, at an availability the drawn table determines.** -/
structure TableFacts (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → Node → Prop)
    (allowed : Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp)) : Prop where
  /-- The handler never fails. -/
  neverFails : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain)
    (state : HandlerState), Pr[⊥ | ((impl table) queried).run state] = 0
  /-- A step grows the carrier. -/
  grows : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState),
    step ∈ support (((impl table) queried).run state) →
      HandlerCarrier.Grows state.1 step.2.1
  /-- A step appends one probe, or none. -/
  record : ∀ (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState),
    step ∈ support (((impl table) queried).run state) →
      step.2.2.1 = state.2.1 ++ appended queried state.1
  /-- **The availability does not read the cell either.** Without this the two sides of a
  comparison would stall at different moments. -/
  availBlind : ∀ (index : Node), allowed index → ∀ (left right : Cells × Padding),
    AgreeOff index left right → availableAt left = availableAt right
  /-- A step at a state where a cell is unavailable does not read that cell — at the indices
  `allowed` admits, and no others. -/
  blind : ∀ (index : Node), allowed index → ∀ (left right : Cells × Padding),
    AgreeOff index left right →
    ∀ (queried : OracleWorld.Domain) (state : HandlerState),
      ¬ availableAt left state.1 index →
        ((impl left) queried).run state = ((impl right) queried).run state

/-- **A fixed availability is the constant case.** So every existing `Facts` instance is a
`TableFacts` instance, and `availBlind` is `rfl` there — a constant reads no cell. -/
theorem tableFacts_of_facts (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (allowed : Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (hfacts : Facts publicSeed availableAt allowed impl) :
    TableFacts publicSeed (fun _ => availableAt) allowed impl where
  neverFails := hfacts.neverFails
  grows := hfacts.grows
  record := hfacts.record
  availBlind _ _ _ _ _ := rfl
  blind := hfacts.blind

end SlhDsaSecurity.HandlerFacts

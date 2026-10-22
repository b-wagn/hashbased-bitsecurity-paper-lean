import SlhDsaSecurity.Proof.CarrierFiles
import SlhDsaSecurity.Proof.ClassGrowth

/-!
# What counts the counted handler admits

The two charges that have to meet over one budget are read, on the cache side, off a **split**
counter: `ClassGrowth.splitCost inClass inside outside` charges each hash call one unit of one
of two slots, and `CoverageCount.prob_bad_or_coverage_le_of_charges` takes the structural clause
at the `outside` slot, the coverage clause at the `inside` slot, and the two inside one budget.

The carrier tail has no such counter. Its count is a single `Nat` in the handler's state, put
there by `CountedHandler.withCount` for the reason that file gives: a bracketed game is not one
computation, so there is nothing for an instrumentation wrapped *around* a computation to wrap.
So the question is what counts the handler admits, and the answer is sharp:

**A counted handler admits exactly the per-query accumulations of a cost into a component beside
the carrier** — the `CountedHandler.withExtra` instances, and nothing else. It does *not* admit
the cache side's count as it stands, because that one is installed on a computation
(`countQueries cost computation` under the plain shared oracle) and `ClassExpectation.
prob_bad_le_expected_cost` inducts over that computation.

That is enough, because the split *is* such an accumulation: `splitCost` is already a
`Domain → Counts`, so the split counter is `withExtra` at `ω := Counts` with the update
`(· + splitCost inClass inside outside queried)` — **the same cost function the cache side
installs**, moved from the computation to the handler. No new notion of cost appears here.

## Why this costs nothing downstream

The obvious way to give the tail two slots is to widen `BracketedRun.CountedState`, and that
would be a shape change under four readers. It is not needed. `run_withSplit_withCount` below
says the split-counted run **is** the counted run with its counter split: map the two slots to
their sum and the split handler becomes `withCount`. So a split tail sits *above* the existing
tail rather than replacing it, and:

* the coverage charge transports **up** the map for free, because `probEvent` and `expected` of
  a mapped run are the run's own — nothing about the tape factorisation is redone;
* the structural charge is stated at the `outside` slot, which is the same proposition the cache
  side's meeting point already takes;
* `hshare` carries no new content: `splitCost_add_eq_hashCost` makes `inside + outside` the
  count the tail already has, so sharing one budget is the budget hypothesis that is already
  there.

`BracketedRun.CountedState`, `IsBracketedRecorderRun`, `CarrierTail.carrierTail` and everything
read off them are untouched.

## The `hcost` side

What a charge's induction needs of a counter is a lower bound per query: an in-class call must
move the slot it is charged to. `withSplit_step_inside` and `withSplit_step_outside` are those
bounds at the handler's step, and they are `splitCost_inside` and `splitCost_outside` with the
step law in front — the same two facts the cache side's `hcost` argument is discharged by.

**The seed charge is not retired, and nothing here assumes it is.** The split partitions the
*hash* calls of a run and sums to that run's own hash count; whatever is charged in seed units
is charged elsewhere and is not touched by either slot.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitCounted

open Security RecorderView HandlerCarrier CarriedWitness ServedAgreement
open CountedHandler ClassGrowth

variable (pk : PublicKey) {τ : Type}

/-- A handler with a two-slot hash counter beside its carrier: one slot for the class, one for
its complement. -/
noncomputable def withSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) :
    QueryImpl OracleWorld (StateT (HandlerCarrier.State × (τ × Counts)) ProbComp) :=
  withExtra impl (fun queried counts => counts + splitCost inClass inside outside queried)

theorem withSplit_run (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Counts)) :
    ((withSplit inClass inside outside impl) queried).run state =
      (impl queried).run (state.1, state.2.1) >>= fun step =>
        (pure (step.1, (step.2.1, (step.2.2,
            state.2.2 + splitCost inClass inside outside queried))) :
          ProbComp (OracleWorld.Range queried × (HandlerCarrier.State × (τ × Counts)))) := rfl

/-- **A step of the split-counted handler is a step of the handler, with the pair bumped.** -/
theorem withSplit_step (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Counts))
    (step : OracleWorld.Range queried × (HandlerCarrier.State × (τ × Counts)))
    (hstep : step ∈ support (((withSplit inClass inside outside impl) queried).run state)) :
    ∃ inner : OracleWorld.Range queried × (HandlerCarrier.State × τ),
      inner ∈ support ((impl queried).run (state.1, state.2.1)) ∧
        step.1 = inner.1 ∧ step.2.1 = inner.2.1 ∧ step.2.2.1 = inner.2.2 ∧
        step.2.2.2 = state.2.2 + splitCost inClass inside outside queried := by
  rw [withSplit_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨inner, hinner, by rw [hpure], by rw [hpure], by rw [hpure], by rw [hpure]⟩

open scoped Classical in
/-- **It files if the handler underneath does.** The pair is an extra component and `Files`
reads only the carrier. -/
theorem files_withSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    {impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)}
    (hfiles : Files pk impl) : Files pk (withSplit inClass inside outside impl) :=
  files_withExtra pk hfiles
    (fun queried counts => counts + splitCost inClass inside outside queried)

/-- **And it forgets wherever the handler underneath does.** -/
theorem forgetsAlong_withSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    {S' : Type} (π : HandlerCarrier.State × τ → S')
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hforget : ServingForget.ForgetsAlong π impl outer') :
    ServingForget.ForgetsAlong (fun state : HandlerCarrier.State × (τ × Counts) =>
      π (state.1, state.2.1)) (withSplit inClass inside outside impl) outer' :=
  forgetsAlong_withExtra π impl
    (fun queried counts => counts + splitCost inClass inside outside queried) outer' hforget

theorem run_withSplit_map (inClass : Bytes → Prop) (inside outside : QueryKind) {α : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Counts),
      (fun z : α × (HandlerCarrier.State × (τ × Counts)) => (z.1, (z.2.1, z.2.2.1))) <$>
          (simulateQ (withSplit inClass inside outside impl) computation).run state =
        (simulateQ impl computation).run (state.1, state.2.1) :=
  run_withExtra_map impl
    (fun queried counts => counts + splitCost inClass inside outside queried) computation

/-! ## The two slots are the counter

This is the lemma that keeps the split off the tail's state. It says the split-counted run is
the counted run with the counter split in two: map a state's pair of slots to their sum and the
whole run becomes `withCount`'s, started at the summed counter.

Everything the no-ripple claim rests on is here. Read right to left it builds a split run over
the existing one; read left to right it carries any event or expectation of the split run down
to the counted one, so the charges can be taken wherever each is easiest and still meet. -/

set_option maxHeartbeats 400000 in
/-- **The split-counted run is the counted run, with the counter split.** -/
theorem run_withSplit_withCount (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Counts),
      (fun z : α × (HandlerCarrier.State × (τ × Counts)) =>
          (z.1, (z.2.1, (z.2.2.1, z.2.2.2 inside + z.2.2.2 outside)))) <$>
          (simulateQ (withSplit inClass inside outside impl) computation).run state =
        (simulateQ (withCount impl) computation).run
          (state.1, (state.2.1, state.2.2 inside + state.2.2 outside)) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, simulateQ_pure, StateT.run_pure]
  | query_bind queried next ih =>
    intro state
    have harith : (state.2.2 + splitCost inClass inside outside queried) inside +
        (state.2.2 + splitCost inClass inside outside queried) outside =
        state.2.2 inside + state.2.2 outside + hashCost queried := by
      rw [Pi.add_apply, Pi.add_apply, ← splitCost_add_eq_hashCost inClass hne queried]
      omega
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, withSplit_run, withCount_run, bind_assoc,
      bind_assoc]
    refine bind_congr fun step => ?_
    rw [pure_bind, pure_bind,
      ih step.1 (step.2.1, (step.2.2, state.2.2 + splitCost inClass inside outside queried)),
      harith]

/-! ## The per-query lower bounds

What a charge reads off a counter is that the query it is charging moved the slot. These are
those two facts at the handler's step; `splitCost_inside` and `splitCost_outside` are where the
content is, and the step law is what puts them at the handler. -/

open scoped Classical in
/-- **An in-class hash call moves the inside slot.** -/
theorem withSplit_step_inside (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (input : Bytes) (hmember : inClass input)
    (state : HandlerCarrier.State × (τ × Counts))
    (step : OracleWorld.Range (Sum.inr input) × (HandlerCarrier.State × (τ × Counts)))
    (hstep : step ∈ support
      (((withSplit inClass inside outside impl) (Sum.inr input)).run state)) :
    state.2.2 inside + 1 ≤ step.2.2.2 inside := by
  classical
  obtain ⟨-, -, -, -, -, hcounts⟩ :=
    withSplit_step inClass inside outside impl (Sum.inr input) state step hstep
  rw [hcounts, Pi.add_apply, splitCost_inside inClass inside outside input hmember]

open scoped Classical in
/-- **An out-of-class hash call moves the outside slot.** -/
theorem withSplit_step_outside (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (input : Bytes) (hmember : ¬ inClass input)
    (state : HandlerCarrier.State × (τ × Counts))
    (step : OracleWorld.Range (Sum.inr input) × (HandlerCarrier.State × (τ × Counts)))
    (hstep : step ∈ support
      (((withSplit inClass inside outside impl) (Sum.inr input)).run state)) :
    state.2.2 outside + 1 ≤ step.2.2.2 outside := by
  classical
  obtain ⟨-, -, -, -, -, hcounts⟩ :=
    withSplit_step inClass inside outside impl (Sum.inr input) state step hstep
  rw [hcounts, Pi.add_apply, splitCost_outside inClass inside outside input hmember]

/-- **Neither slot moves on a coin.** -/
theorem withSplit_step_coin (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (coin : unifSpec.Domain) (state : HandlerCarrier.State × (τ × Counts))
    (step : OracleWorld.Range (Sum.inl coin) × (HandlerCarrier.State × (τ × Counts)))
    (hstep : step ∈ support
      (((withSplit inClass inside outside impl) (Sum.inl coin)).run state)) :
    step.2.2.2 = state.2.2 := by
  obtain ⟨-, -, -, -, -, hcounts⟩ :=
    withSplit_step inClass inside outside impl (Sum.inl coin) state step hstep
  rw [hcounts, splitCost_inl, add_zero]

/-! ## At the carrier

The tail's handler is `CarrierFiles.countedCarrierRecorder`, which is `withCount` around the
recorder that notices. Its split counterpart is the same recorder under `withSplit`, and the
three laws the tail reads a handler through come back unchanged. -/

/-- The handler a split-counted carrier tail runs under. -/
noncomputable def splitCarrierRecorder (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    QueryImpl OracleWorld
      (StateT (HandlerCarrier.State ×
        ((DigestTape.Record × DigestTape.Record) × Counts)) ProbComp) :=
  withSplit inClass inside outside
    (@noticingRecorderOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep)

open scoped Classical in
/-- **It files.** -/
theorem files_splitCarrierRecorder (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    Files pk (splitCarrierRecorder pk inClass inside outside rightKeep) :=
  files_withSplit pk inClass inside outside (CarrierFiles.files_carrierRecorder pk rightKeep)

/-- **And it forgets to the shared oracle.** -/
theorem forgetsAlong_splitCarrierRecorder (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Bytes → HandlerCarrier.State → Prop) :
    ServingForget.ForgetsAlong
      (fun state : HandlerCarrier.State ×
          ((DigestTape.Record × DigestTape.Record) × Counts) =>
        CacheView.cacheOf (state.1, state.2.1).1)
      (splitCarrierRecorder pk inClass inside outside rightKeep) KeygenUniform.rom :=
  forgetsAlong_withSplit inClass inside outside
    (fun state : StateOf HandlerCarrier.State => CacheView.cacheOf state.1) _ KeygenUniform.rom
    (CarrierFiles.forgetsAlong_carrierRecorder pk rightKeep)

/-- **The split carrier recorder is the counted one, with the counter split.** The carrier
instance of `run_withSplit_withCount`, and the statement a split tail is carried onto the
existing tail by. -/
theorem run_splitCarrierRecorder_counted (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (rightKeep : Bytes → HandlerCarrier.State → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts),
      (fun z : α × (HandlerCarrier.State ×
            ((DigestTape.Record × DigestTape.Record) × Counts)) =>
          (z.1, (z.2.1, (z.2.2.1, z.2.2.2 inside + z.2.2.2 outside)))) <$>
          (simulateQ (splitCarrierRecorder pk inClass inside outside rightKeep)
            computation).run state =
        (simulateQ (CarrierFiles.countedCarrierRecorder pk rightKeep) computation).run
          (state.1, (state.2.1, state.2.2 inside + state.2.2 outside)) :=
  run_withSplit_withCount inClass hne _ computation

end SlhDsaSecurity.SplitCounted

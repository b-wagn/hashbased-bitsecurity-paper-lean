import SlhDsaSecurity.Proof.RecordInvariant
import SlhDsaSecurity.Proof.CarrierFiles

/-!
# What the counted recorder keeps true of its target recording

The two instances of `RecordInvariant`, and the one place the recorder's own shape enters.

Each is a step fact and nothing else: a step of the counted recorder appends at most its own
query's entry to the target recording, and when it does, the query was fresh and the right test
held at the state the notice had already reached. `RecorderView.appendedOf_right_mem` says that
of the recorder, `CountedHandler.withCount_step` carries it through the counter, and
`RecordInvariant` carries it through runs and brackets.

Both invariants read only the cache and the recordings, so `RecordInvariant.bracket_invariant`
discharges their bracket condition rather than asking for it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierRecordings

open Security BracketedRun RecorderView CarriedWitness CarrierFiles RecordInvariant
  CountedHandler

variable (pk : PublicKey)

/-! ## One step of the counted recorder -/

open scoped Classical in
/-- **A step appends at most its own query's entry**, and when it does, the query was fresh, the
right test held at the state the notice had reached, and the step left that entry cached.

The last conjunct is there because the second consumer needs it: one invariant reads the test,
the other reads the caching, and an entry whose test is reported without its caching sends the
caller back to the step it was already handed. -/
theorem step_right_mem (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) queried).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ step.2.2.1.2) :
    entry ∈ state.2.1.2 ∨
      ∃ view : HandlerCarrier.State, view.cache = state.1.cache ∧
        view.cache entry.1 = none ∧ rightKeep entry.1 view ∧
          step.2.1.cache entry.1 = some entry.2 := by
  classical
  obtain ⟨inner, hinner, hvalue, -, hcarried⟩ := withCount_step _ queried state step hstep
  rw [hcarried] at hentry
  rcases queried with coin | input
  · rw [show inner.2.2 = (state.1, state.2.1).2 from
      congrArg Prod.snd (@recorderOf_step_inl HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep coin (state.1, state.2.1) inner
        (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk)]; exact
          hinner))] at hentry
    exact Or.inl hentry
  · have hinr := hinner
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1)] at hinr
    rw [@recorderOf_step_record HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner hinr] at hentry
    rcases @appendedOf_right_mem HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner.1 entry hentry with hprior | ⟨hself, hfresh, hright⟩
    · exact Or.inl hprior
    · have hinput : entry.1 = input := by rw [hself]
      have hanswer : entry.2 = step.1 := by rw [hself, hvalue]
      refine Or.inr ⟨servingNotice pk state.1 input, cacheOf_servingNotice pk state.1 input,
        ?_, ?_, ?_⟩
      · rw [hinput]
        exact hfresh
      · rw [hinput]
        exact hright
      · rw [hinput, hanswer]
        exact (files_countedCarrierRecorder pk rightKeep).hashCached input state step hstep

/-! ## The two invariants -/

/-- **Every target-recorded input is of the narrowed class.** -/
def RecordClass (narrow : Bytes → Prop) (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.2, narrow entry.1

/-- **Every target-recorded input is cached**, so it was fresh exactly once. -/
def RecordCached (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.2, state.1.cache entry.1 ≠ none

theorem recordClass_bracket (narrow : Bytes → Prop) {f : CountedState → CountedState}
    (hf : Bracket f) (state : CountedState) (hinv : RecordClass narrow state) :
    RecordClass narrow (f state) := by
  intro entry hentry
  rw [(hf state).2] at hentry
  exact hinv entry hentry

theorem recordCached_bracket {f : CountedState → CountedState} (hf : Bracket f)
    (state : CountedState) (hinv : RecordCached state) : RecordCached (f state) := by
  intro entry hentry
  rw [(hf state).2] at hentry
  rw [(hf state).1]
  exact hinv entry hentry

open scoped Classical in
/-- **The class invariant's step fact.** The right test keeps only the narrowed class, so an
entry the step appended is of it. -/
theorem step_recordClass (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (narrow : Bytes → Prop)
    (hnarrow : ∀ (input : Bytes) (view : HandlerCarrier.State), rightKeep input view →
      narrow input)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) queried).run state))
    (hinv : RecordClass narrow state) : RecordClass narrow step.2 := by
  intro entry hentry
  rcases step_right_mem pk rightKeep queried state step hstep entry hentry with
    hprior | ⟨view, -, -, hright, -⟩
  · exact hinv entry hprior
  · exact hnarrow entry.1 view hright

open scoped Classical in
/-- **The cached invariant's step fact.** An entry already recorded stays cached because the
carrier only grows; the entry a step appends is cached by that step. The two halves come from
the two interfaces — the recording side says which entry was appended, the carrier side says
the carrier grew — which is what one interface per component is for. -/
theorem step_recordCached (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) queried).run state))
    (hinv : RecordCached state) : RecordCached step.2 := by
  classical
  intro entry hentry
  rcases step_right_mem pk rightKeep queried state step hstep entry hentry with
    hprior | ⟨-, -, -, -, hcached⟩
  · obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp (hinv entry hprior)
    rw [((files_countedCarrierRecorder pk rightKeep).stepGrows queried state step hstep).1
      entry.1 value hvalue]
    simp
  · rw [hcached]
    simp

end SlhDsaSecurity.CarrierRecordings

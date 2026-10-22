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

open scoped Classical in
/-- **The target recording after a step, as a list**, with the appended entry's freshness and
the test it passed. The shape reading of the step, which an invariant about multiplicity needs
and membership cannot give — and the test besides, because the witness lemma built on this one
has to say what the entry was filed for. -/
theorem step_right_shape (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) queried).run state)) :
    step.2.2.1.2 = state.2.1.2 ∨
      ∃ pair : Bytes × HashOutput, step.2.2.1.2 = state.2.1.2 ++ [pair] ∧
        state.1.cache pair.1 = none ∧
          rightKeep pair.1 (servingNotice pk state.1 pair.1) := by
  classical
  obtain ⟨inner, hinner, hvalue, -, hcarried⟩ := withCount_step _ queried state step hstep
  rcases queried with coin | input
  · refine Or.inl ?_
    rw [hcarried, show inner.2.2 = (state.1, state.2.1).2 from
      congrArg Prod.snd (@recorderOf_step_inl HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep coin (state.1, state.2.1) inner
        (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk)]; exact
          hinner))]
  · have hinr := hinner
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1)] at hinr
    rw [hcarried, @recorderOf_step_record HandlerCarrier.State (servingView pk)
      (disclosingKeep pk) rightKeep input _ inner hinr]
    rcases @appendedOf_right_shape HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner.1 with hsame | ⟨hshape, hfresh, hright⟩
    · exact Or.inl hsame
    · refine Or.inr ⟨(input, inner.1), hshape, ?_, hright⟩
      show HandlerCarrier.cacheOf state.1 input = none
      rw [← cacheOf_servingNotice pk state.1 input]
      exact hfresh

/-! ## And the state each filed entry was filed at

`SplitPrefix.right_record_suffix` at the carrier. An invariant says what is true of the whole
recording; this says, of each entry, the state it was filed at — which is what a provenance
argument needs and an invariant cannot give. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Every entry a run files as a target comes with the carrier it was filed at**: fresh there,
passing the right test at the state the notice had reached, and contained in the run's own
carrier afterwards. -/
theorem run_right_suffix (rightKeep : Bytes → HandlerCarrier.State → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : CountedState) (result : α × CountedState),
      result ∈ support ((simulateQ (countedCarrierRecorder pk rightKeep) computation).run
        state) →
        ∃ suffix : DigestTape.Record, result.2.2.1.2 = state.2.1.2 ++ suffix ∧
          ∀ entry ∈ suffix, ∃ mid : HandlerCarrier.State,
            (∀ (probe : Bytes) (value : HashOutput),
              state.1.cache probe = some value → mid.cache probe = some value) ∧
            (∀ (probe : Bytes) (value : HashOutput),
              mid.cache probe = some value → result.2.1.cache probe = some value) ∧
              mid.cache entry.1 = none ∧
                rightKeep entry.1 (servingNotice pk mid entry.1) := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact ⟨[], (List.append_nil _).symm, fun entry hentry => absurd hentry (by simp)⟩
  | query_bind queried next ih =>
    intro state result hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨suffix, hsuffix, hentries⟩ := ih step.1 step.2 result hrest
    have hstepGrow := ((files_countedCarrierRecorder pk rightKeep).stepGrows queried state step
      hstep).1
    rcases step_right_shape pk rightKeep queried state step hstep with
      hsame | ⟨pair, hshape, hfresh, hright⟩
    · refine ⟨suffix, by rw [hsuffix, hsame], fun entry hentry => ?_⟩
      obtain ⟨mid, hstart, hlater, habsent, hkeep⟩ := hentries entry hentry
      exact ⟨mid, fun probe value hvalue => hstart probe value (hstepGrow probe value hvalue),
        hlater, habsent, hkeep⟩
    · refine ⟨pair :: suffix, by rw [hsuffix, hshape, List.append_assoc]; rfl,
        fun entry hentry => ?_⟩
      rcases List.mem_cons.mp hentry with hself | hlater
      · refine ⟨state.1, fun _ _ hvalue => hvalue, fun probe value hvalue => ?_, ?_, ?_⟩
        · exact ((files_countedCarrierRecorder pk rightKeep).runPersists (next step.1) step.2
            result hrest).1 probe value (hstepGrow probe value hvalue)
        · rw [hself]
          exact hfresh
        · rw [hself]
          exact hright
      · obtain ⟨mid, hstart, hmidLater, habsent, hkeep⟩ := hentries entry hlater
        exact ⟨mid, fun probe value hvalue => hstart probe value (hstepGrow probe value hvalue),
          hmidLater, habsent, hkeep⟩

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

/-! ## And each input once

Carried with `RecordCached`, because that is what proves it: an entry is appended only when its
input is fresh, and every entry already recorded is cached, so the new one is none of them. The
two halves travel together for the same reason the step fact reports both. -/

/-- **The target recording is cached and holds each input once.** -/
def RecordFreshNodup (state : CountedState) : Prop :=
  RecordCached state ∧ (state.2.1.2.map Prod.fst).Nodup

theorem recordFreshNodup_bracket {f : CountedState → CountedState} (hf : Bracket f)
    (state : CountedState) (hinv : RecordFreshNodup state) : RecordFreshNodup (f state) := by
  refine ⟨recordCached_bracket hf state hinv.1, ?_⟩
  rw [(hf state).2]
  exact hinv.2

open scoped Classical in
/-- **The step fact.** The appended input was fresh, every recorded input is cached, so the two
cannot coincide. -/
theorem step_recordFreshNodup (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) queried).run state))
    (hinv : RecordFreshNodup state) : RecordFreshNodup step.2 := by
  classical
  refine ⟨step_recordCached pk rightKeep queried state step hstep hinv.1, ?_⟩
  rcases step_right_shape pk rightKeep queried state step hstep with
    hsame | ⟨pair, hshape, hfresh, -⟩
  · rw [hsame]
    exact hinv.2
  · rw [hshape, List.map_append]
    refine List.Nodup.append hinv.2 (by simp) ?_
    intro probe hprior hnew
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hnew
    obtain ⟨prior, hpriorMem, hpriorInput⟩ := List.mem_map.mp hprior
    refine absurd hfresh ?_
    rw [← hnew, ← hpriorInput]
    exact hinv.1 prior hpriorMem

end SlhDsaSecurity.CarrierRecordings

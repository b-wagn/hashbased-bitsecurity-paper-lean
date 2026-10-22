import SlhDsaSecurity.Proof.DigestTape
import SlhDsaSecurity.Proof.SplitPrefix

/-!
# The recording, read off a tape drawn in advance

`DigestTape.prob_tape_event_le` carries a recorded run to a uniform tape by a union bound over
the words the event is witnessed by, and that is where the coverage charge loses the per-run
weight it needs: the bound `Pr[word ⊑ record] ≤ 2 ^ -128 · |word|` is all it keeps, and that is
compatible with a run whose whole mass sits on bad words of one length. What is thrown away is
the conditional uniformity of the recording *given its length*.

This file keeps it, by drawing the tape first. `tapeRecorder` is the recording oracle with its
fresh class answers taken off a list fixed in advance instead of drawn on the spot, falling back
to a draw when the list is spent — so no length hypothesis is needed anywhere and the
factorisation is an identity rather than a bound.

What makes this cheaper than a derandomisation of the game is what the identity is *for*. The
leave-one-out charge resamples one tape coordinate and needs the disclosure set, the load
condition and the selection of the coordinate all to survive the overwrite. Only the class
answers have to come off a tape for that: the coins and the out-of-class answers may stay inline,
because the selection has to be *causal*, not deterministic. So a single front block of class
answers is all that is front-loaded here, and everything else keeps drawing where it did.

The induction has one case that does any work. A coin, a cache hit and an out-of-class miss are
all answer-irrelevant to the front block, so the block commutes past them
(`DeferredSampling.evalDist_bind_comm`); a fresh class query splices one answer off the head of
the block, which is `DigestTape.padding`'s own shape; and the spent remainder of the block is
dropped at the end by `DeferredSampling.evalDist_bind_const_neverFails`.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TapeFactor

open DigestTape

/-- The cache, the unread remainder of the tape, and the recording so far. -/
abbrev TapeState := QueryCache HashSpec × List HashOutput × Record

/-- The tape-reading run, read as an ordinary recorded run: the unread remainder is dropped. -/
def forget {α : Type} (result : α × TapeState) : α × RecordState :=
  (result.1, (result.2.1, result.2.2.2))

open scoped Classical in
/-- **The recording oracle with its class answers read off a tape.** A fresh query whose input
passes `keep` takes the head of the tape as its answer; everything else draws as before, and so
does a class query made after the tape is spent. -/
noncomputable def tapeRecorder (keep : Bytes → Prop) :
    QueryImpl OracleWorld (StateT TapeState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        if keep input ∧ state.1 input = none then
          match state.2.1 with
          | head :: rest =>
              (pure (head, (state.1.cacheQuery input head, rest,
                state.2.2 ++ [(input, head)])) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (state.1.cacheQuery input value, ([] : List HashOutput),
                state.2.2 ++ [(input, value)]))
        else do
          let step ← (randomOracle input).run state.1
          pure (step.1, (step.2, state.2.1, state.2.2))

open scoped Classical in
theorem tapeRecorder_run_inl (keep : Bytes → Prop) (coin : unifSpec.Domain)
    (state : TapeState) :
    ((tapeRecorder keep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
/-- Off the class, or on a repeat, the tape is untouched and the oracle draws as before. -/
theorem tapeRecorder_run_inr_other (keep : Bytes → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (tape : List HashOutput) (record : Record)
    (hskip : ¬ (keep input ∧ cache input = none)) :
    ((tapeRecorder keep) (Sum.inr input)).run (cache, tape, record) =
      (randomOracle input).run cache >>= fun step =>
        (pure (step.1, (step.2, tape, record)) : ProbComp _) := by
  classical
  simp only [tapeRecorder, StateT.run]
  rw [if_neg hskip]

open scoped Classical in
/-- A fresh class query takes the head of the tape. -/
theorem tapeRecorder_run_inr_cons (keep : Bytes → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (head : HashOutput) (rest : List HashOutput)
    (record : Record) (hkeep : keep input) (hfresh : cache input = none) :
    ((tapeRecorder keep) (Sum.inr input)).run (cache, head :: rest, record) =
      (pure (head, (cache.cacheQuery input head, rest, record ++ [(input, head)])) :
        ProbComp _) := by
  classical
  simp only [tapeRecorder, StateT.run]
  rw [if_pos ⟨hkeep, hfresh⟩]

open scoped Classical in
/-- Once the tape is spent a class query draws like any other. -/
theorem tapeRecorder_run_inr_nil (keep : Bytes → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (record : Record)
    (hkeep : keep input) (hfresh : cache input = none) :
    ((tapeRecorder keep) (Sum.inr input)).run (cache, [], record) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value, ([] : List HashOutput),
          record ++ [(input, value)])) : ProbComp _) := by
  classical
  simp only [tapeRecorder, StateT.run]
  rw [if_pos ⟨hkeep, hfresh⟩]

open scoped Classical in
/-- The recording oracle's own shape at a fresh class query. -/
theorem recorder_run_inr_fresh (keep : Bytes → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (record : Record)
    (hkeep : keep input) (hfresh : cache input = none) :
    ((recorder keep) (Sum.inr input)).run (cache, record) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value, record ++ [(input, value)])) :
          ProbComp _) := by
  classical
  rw [recorder_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
  funext value
  rw [if_pos ⟨hkeep, hfresh⟩]

open scoped Classical in
/-- The recording oracle's shape off the class, or on a repeat. -/
theorem recorder_run_inr_other (keep : Bytes → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (record : Record)
    (hskip : ¬ (keep input ∧ cache input = none)) :
    ((recorder keep) (Sum.inr input)).run (cache, record) =
      (randomOracle input).run cache >>= fun step =>
        (pure (step.1, (step.2, record)) : ProbComp _) := by
  classical
  rw [recorder_run_inr]
  refine congrArg (fun step => (randomOracle input).run cache >>= step) ?_
  funext step
  rw [if_neg hskip]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The recorded run factorises through a tape drawn in advance.** Drawing a block of
`length` uniform answers first and reading the fresh class answers off it is the recorded run
itself, for every `length` — the block is neither required to be long enough nor allowed to
matter when it is too long. -/
theorem evalDist_tapeRun (keep : Bytes → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) :
    ∀ (length : Nat) (cache : QueryCache HashSpec) (record : Record),
      𝒟[(simulateQ (recorder keep) computation).run (cache, record)] =
        𝒟[padding length >>= fun tape =>
            forget <$> (simulateQ (tapeRecorder keep) computation).run
              (cache, tape, record)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro length cache record
    simp only [simulateQ_pure, StateT.run_pure]
    rw [show (fun tape : List HashOutput =>
          forget <$> (pure (value, (cache, tape, record)) : ProbComp (α × TapeState))) =
        fun _ : List HashOutput =>
          (pure (value, (cache, record)) : ProbComp (α × RecordState)) from by
      funext tape
      rw [map_pure]
      rfl]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding length)
      (padding_neverFails length) _).symm
  | query_bind queried next ih =>
    intro length cache record
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · -- A coin is answer-irrelevant to the block, so the block commutes past it.
      simp only [recorder_run_inl, tapeRecorder_run_inl, bind_assoc, pure_bind, map_bind]
      rw [OracleComp.DeferredSampling.evalDist_bind_congr_left
        ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) _
        (fun value => padding length >>= fun tape =>
          forget <$> (simulateQ (tapeRecorder keep) (next value)).run (cache, tape, record))
        (fun value => ih value length cache record)]
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding length) _
    · by_cases hskip : keep input ∧ cache input = none
      · -- A fresh class query splices one answer off the head of the block.
        obtain ⟨hkeep, hfresh⟩ := hskip
        rw [recorder_run_inr_fresh keep input cache record hkeep hfresh]
        simp only [bind_assoc, pure_bind]
        cases length with
        | zero =>
          rw [padding]
          simp only [pure_bind]
          rw [tapeRecorder_run_inr_nil keep input cache record hkeep hfresh]
          simp only [bind_assoc, pure_bind, map_bind]
          exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
            fun value => by
              rw [ih value 0 (cache.cacheQuery input value) (record ++ [(input, value)]),
                padding]
              simp only [pure_bind]
        | succ remaining =>
          rw [show padding (remaining + 1) =
              ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
                padding remaining >>= fun rest =>
                  (pure (value :: rest) : ProbComp _) from rfl]
          simp only [bind_assoc, pure_bind]
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun value => ?_
          rw [ih value remaining (cache.cacheQuery input value) (record ++ [(input, value)])]
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun rest => ?_
          rw [tapeRecorder_run_inr_cons keep input cache value rest record hkeep hfresh]
          simp only [pure_bind]
      · -- A cache hit or an out-of-class miss is answer-irrelevant to the block.
        rw [recorder_run_inr_other keep input cache record hskip]
        simp only [bind_assoc, pure_bind, map_bind]
        rw [show (fun tape : List HashOutput =>
              ((tapeRecorder keep) (Sum.inr input)).run (cache, tape, record) >>= fun step =>
                forget <$> (simulateQ (tapeRecorder keep) (next step.1)).run step.2) =
            fun tape : List HashOutput =>
              (randomOracle input).run cache >>= fun step =>
                forget <$> (simulateQ (tapeRecorder keep) (next step.1)).run
                  (step.2, tape, record) from by
          funext tape
          rw [tapeRecorder_run_inr_other keep input cache tape record hskip]
          simp only [bind_assoc, pure_bind]]
        rw [OracleComp.DeferredSampling.evalDist_bind_congr_left
          ((randomOracle input).run cache) _
          (fun step => padding length >>= fun tape =>
            forget <$> (simulateQ (tapeRecorder keep) (next step.1)).run
              (step.2, tape, record))
          (fun step => ih step.1 length step.2 record)]
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding length) _

/-! ## Normalising a block at the head of a bind

Both factorisations read their blocks head-first, so the two shapes a block takes under a bind
are worth having as rewrites that go under a binder: a spent block disappears, and a block with
one more answer splits into that answer and the rest. -/

theorem padding_zero_bind {γ : Type} (continuation : List HashOutput → ProbComp γ) :
    padding 0 >>= continuation = continuation [] := by
  rw [padding]
  simp only [pure_bind]

theorem padding_succ_bind {γ : Type} (length : Nat)
    (continuation : List HashOutput → ProbComp γ) :
    padding (length + 1) >>= continuation =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding length >>= fun rest => continuation (value :: rest) := by
  rw [padding]
  simp only [bind_assoc, pure_bind]

/-! ## Two blocks, one for each role

The coverage charge needs the disclosing answers and the target answers on *separately drawn*
blocks, because the resampling it runs on overwrites one target coordinate and requires the
disclosure set not to move. With one block the two roles interleave at run-dependent positions
and nothing is fixed; with two, the disclosures are a function of a block the overwrite does not
touch.

The induction is the one above with its drawing case split in two. Each block splices its own
head, and whichever block is not being read commutes past the step like any other
answer-irrelevant draw. -/

/-- The cache, the unread remainders of the two blocks, and the two recordings. -/
abbrev SplitTapeState :=
  QueryCache HashSpec × (List HashOutput × List HashOutput) × (Record × Record)

/-- The two-headed tape-reading run, read as an ordinary two-recording run. -/
def forgetSplit {α : Type} (result : α × SplitTapeState) : α × SplitPrefix.SplitState :=
  (result.1, (result.2.1, result.2.2.2))

open scoped Classical in
/-- **The two-recording oracle with each role's answers read off its own block.** The left test
is tried first, so one answer is never read off both blocks. -/
noncomputable def splitTapeRecorder
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) :
    QueryImpl OracleWorld (StateT SplitTapeState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        if state.1 input = none ∧ leftKeep input state.1 then
          match state.2.1.1 with
          | head :: rest =>
              (pure (head, (state.1.cacheQuery input head, (rest, state.2.1.2),
                (state.2.2.1 ++ [(input, head)], state.2.2.2))) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (state.1.cacheQuery input value,
                (([] : List HashOutput), state.2.1.2),
                (state.2.2.1 ++ [(input, value)], state.2.2.2)))
        else if state.1 input = none ∧ rightKeep input state.1 then
          match state.2.1.2 with
          | head :: rest =>
              (pure (head, (state.1.cacheQuery input head, (state.2.1.1, rest),
                (state.2.2.1, state.2.2.2 ++ [(input, head)]))) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (state.1.cacheQuery input value,
                (state.2.1.1, ([] : List HashOutput)),
                (state.2.2.1, state.2.2.2 ++ [(input, value)])))
        else do
          let step ← (randomOracle input).run state.1
          pure (step.1, (step.2, state.2.1, state.2.2))

/-! ### The step shapes -/

open scoped Classical in
theorem splitTapeRecorder_run_inl
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (coin : unifSpec.Domain)
    (state : SplitTapeState) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem splitTapeRecorder_run_left_cons
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (head : HashOutput) (rest rightTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : leftKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (head :: rest, rightTape), (leftRecord, rightRecord)) =
      (pure (head, (cache.cacheQuery input head, (rest, rightTape),
        (leftRecord ++ [(input, head)], rightRecord))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem splitTapeRecorder_run_left_nil
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (rightTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : leftKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, ([], rightTape), (leftRecord, rightRecord)) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value, (([] : List HashOutput), rightTape),
          (leftRecord ++ [(input, value)], rightRecord))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem splitTapeRecorder_run_right_cons
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (leftTape : List HashOutput) (head : HashOutput)
    (rest : List HashOutput) (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : ¬ leftKeep input cache)
    (hright : rightKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (leftTape, head :: rest), (leftRecord, rightRecord)) =
      (pure (head, (cache.cacheQuery input head, (leftTape, rest),
        (leftRecord, rightRecord ++ [(input, head)]))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg (fun h => hleft h.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem splitTapeRecorder_run_right_nil
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (leftTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : ¬ leftKeep input cache)
    (hright : rightKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (leftTape, []), (leftRecord, rightRecord)) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value, (leftTape, ([] : List HashOutput)),
          (leftRecord, rightRecord ++ [(input, value)]))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg (fun h => hleft h.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem splitTapeRecorder_run_other
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (tapes : List HashOutput × List HashOutput)
    (records : Record × Record)
    (hskip : ¬ (cache input = none ∧ leftKeep input cache))
    (hskip' : ¬ (cache input = none ∧ rightKeep input cache)) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run (cache, tapes, records) =
      (randomOracle input).run cache >>= fun step =>
        (pure (step.1, (step.2, tapes, records)) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg hskip, if_neg hskip']

/-! ### The same shapes for the drawing recorder -/

open scoped Classical in
theorem splitRecorder_run_left
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : leftKeep input cache) :
    ((SplitPrefix.recorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, leftRecord, rightRecord) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value,
          (leftRecord ++ [(input, value)], rightRecord))) : ProbComp _) := by
  classical
  rw [SplitPrefix.recorder_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
  funext value
  rw [SplitPrefix.appended, if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem splitRecorder_run_right
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (leftRecord rightRecord : Record)
    (hfresh : cache input = none) (hleft : ¬ leftKeep input cache)
    (hright : rightKeep input cache) :
    ((SplitPrefix.recorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, leftRecord, rightRecord) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (cache.cacheQuery input value,
          (leftRecord, rightRecord ++ [(input, value)]))) : ProbComp _) := by
  classical
  rw [SplitPrefix.recorder_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
  funext value
  rw [SplitPrefix.appended, if_neg (fun h => hleft h.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem splitRecorder_run_other
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (records : Record × Record)
    (hskip : ¬ (cache input = none ∧ leftKeep input cache))
    (hskip' : ¬ (cache input = none ∧ rightKeep input cache)) :
    ((SplitPrefix.recorder leftKeep rightKeep) (Sum.inr input)).run (cache, records) =
      (randomOracle input).run cache >>= fun step =>
        (pure (step.1, (step.2, records)) : ProbComp _) := by
  classical
  rw [SplitPrefix.recorder_run_inr]
  refine congrArg (fun step => (randomOracle input).run cache >>= step) ?_
  funext step
  rw [SplitPrefix.appended, if_neg hskip, if_neg hskip']

/-! ### The two blocks commute past an irrelevant draw -/

/-- A draw neither block answers commutes past both of them. -/
theorem evalDist_comm_blocks {β γ : Type} (draw : ProbComp β)
    (leftLength rightLength : Nat)
    (continuation : β → List HashOutput → List HashOutput → ProbComp γ) :
    𝒟[draw >>= fun value => padding leftLength >>= fun leftTape =>
        padding rightLength >>= fun rightTape => continuation value leftTape rightTape] =
      𝒟[padding leftLength >>= fun leftTape => padding rightLength >>= fun rightTape =>
        draw >>= fun value => continuation value leftTape rightTape] := by
  rw [OracleComp.DeferredSampling.evalDist_bind_comm draw (padding leftLength)
    (fun value leftTape => padding rightLength >>= fun rightTape =>
      continuation value leftTape rightTape)]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left (padding leftLength) _ _
    fun leftTape => ?_
  exact OracleComp.DeferredSampling.evalDist_bind_comm draw (padding rightLength)
    fun value rightTape => continuation value leftTape rightTape

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The two-recording run factorises through two blocks drawn in advance.** -/
theorem evalDist_splitTapeRun (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (leftLength rightLength : Nat) (cache : QueryCache HashSpec)
      (leftRecord rightRecord : Record),
      𝒟[(simulateQ (SplitPrefix.recorder leftKeep rightKeep) computation).run
          (cache, leftRecord, rightRecord)] =
        𝒟[padding leftLength >>= fun leftTape =>
            padding rightLength >>= fun rightTape =>
              forgetSplit <$>
                (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
                  (cache, (leftTape, rightTape), (leftRecord, rightRecord))] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, map_pure, forgetSplit]
    rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding leftLength)
      (padding_neverFails leftLength),
      OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding rightLength)
      (padding_neverFails rightLength)]
  | query_bind queried next ih =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · simp only [SplitPrefix.recorder_run_inl, splitTapeRecorder_run_inl, bind_assoc,
        pure_bind, map_bind]
      refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
        (fun value => ih value leftLength rightLength cache leftRecord rightRecord)) ?_
      exact evalDist_comm_blocks _ leftLength rightLength _
    · by_cases hfresh : cache input = none
      · by_cases hleft : leftKeep input cache
        · -- A fresh left-class query splices the head of the left block.
          simp only [splitRecorder_run_left leftKeep rightKeep input cache leftRecord
            rightRecord hfresh hleft, bind_assoc, pure_bind]
          cases leftLength with
          | zero =>
            simp only [padding_zero_bind,
              splitTapeRecorder_run_left_nil leftKeep rightKeep input cache _ leftRecord
                rightRecord hfresh hleft, bind_assoc, pure_bind, map_bind]
            refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              (fun value => ih value 0 rightLength (cache.cacheQuery input value)
                (leftRecord ++ [(input, value)]) rightRecord)) ?_
            simp only [padding_zero_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding rightLength) _
          | succ remaining =>
            simp only [padding_succ_bind,
              splitTapeRecorder_run_left_cons leftKeep rightKeep input cache _ _ _ leftRecord
                rightRecord hfresh hleft, pure_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              fun value => ih value remaining rightLength (cache.cacheQuery input value)
                (leftRecord ++ [(input, value)]) rightRecord
        · by_cases hright : rightKeep input cache
          · -- A fresh right-class query splices the head of the right block.
            simp only [splitRecorder_run_right leftKeep rightKeep input cache leftRecord
              rightRecord hfresh hleft hright, bind_assoc, pure_bind]
            cases rightLength with
            | zero =>
              simp only [padding_zero_bind,
                splitTapeRecorder_run_right_nil leftKeep rightKeep input cache _ leftRecord
                  rightRecord hfresh hleft hright, bind_assoc, pure_bind, map_bind]
              refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
                (fun value => ih value leftLength 0 (cache.cacheQuery input value) leftRecord
                  (rightRecord ++ [(input, value)]))) ?_
              simp only [padding_zero_bind]
              exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding leftLength) _
            | succ remaining =>
              simp only [padding_succ_bind,
                splitTapeRecorder_run_right_cons leftKeep rightKeep input cache _ _ _
                  leftRecord rightRecord hfresh hleft hright, pure_bind]
              refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
                (fun value => ih value leftLength remaining (cache.cacheQuery input value)
                  leftRecord (rightRecord ++ [(input, value)]))) ?_
              exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding leftLength) _
          · -- Neither class: the step is answer-irrelevant to both blocks.
            simp only [splitRecorder_run_other leftKeep rightKeep input cache
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              splitTapeRecorder_run_other leftKeep rightKeep input cache _
                (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind, map_bind]
            refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              (fun step => ih step.1 leftLength rightLength step.2 leftRecord
                rightRecord)) ?_
            exact evalDist_comm_blocks _ leftLength rightLength _
      · -- A cache hit: the step is answer-irrelevant to both blocks.
        simp only [splitRecorder_run_other leftKeep rightKeep input cache
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          splitTapeRecorder_run_other leftKeep rightKeep input cache _
            (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind, map_bind]
        refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
          (fun step => ih step.1 leftLength rightLength step.2 leftRecord rightRecord)) ?_
        exact evalDist_comm_blocks _ leftLength rightLength _

end SlhDsaSecurity.TapeFactor

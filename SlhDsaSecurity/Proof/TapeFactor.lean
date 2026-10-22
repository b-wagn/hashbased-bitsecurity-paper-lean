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

/-! ## Overwriting an unread block cell

The charge resamples one cell of the target block and needs the *selection* of that cell — the
run having got as far as reading it — to hold still. It does, and for the plainest reason: the
run reads cell `index` of the target block when it makes its `index + 1`-st target query, and
whether it makes that query is settled before. So the event "the target recording grows by more
than `index`" has the same probability under any overwrite of cell `index`.

This is a statement about *conditional* probabilities, and that is what makes the whole route
affordable: the run keeps its coins and its out-of-class answers inline, and only the two class
blocks have to be front-loaded. A selection that had to be a *function* of the block would need
every draw the run makes to be presampled instead.

Past the cell the two runs do diverge — they cache different answers at the same input — so the
induction cannot be carried through it. It does not have to be: at the step that reads the cell
the event has already come true, and a recording that only grows keeps it true. -/

/-- The target recording of a state. -/
def rightOf (state : SplitTapeState) : Record := state.2.2.2

open scoped Classical in
/-- **One step never fails and appends at most one target entry.** Both halves of this are what
the selection argument needs, and both are read off the same case split. -/
theorem splitTapeRecorder_step (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (state : SplitTapeState) :
    Pr[⊥ | ((splitTapeRecorder leftKeep rightKeep) queried).run state] = 0 ∧
      ∀ step ∈ support (((splitTapeRecorder leftKeep rightKeep) queried).run state),
        rightOf state <+: rightOf step.2 := by
  classical
  obtain ⟨cache, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
  rcases queried with coin | input
  · rw [splitTapeRecorder_run_inl]
    refine ⟨by simp, fun step hstep => ?_⟩
    rw [mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
  · by_cases hfresh : cache input = none
    · by_cases hleft : leftKeep input cache
      · cases leftTape with
        | nil =>
          rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input cache rightTape
            leftRecord rightRecord hfresh hleft]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_rfl
        | cons head rest =>
          rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input cache head rest
            rightTape leftRecord rightRecord hfresh hleft]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [support_pure, Set.mem_singleton_iff] at hstep
          rw [hstep]
          exact List.prefix_rfl
      · by_cases hright : rightKeep input cache
        · cases rightTape with
          | nil =>
            rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input cache leftTape
              leftRecord rightRecord hfresh hleft hright]
            refine ⟨by simp, fun step hstep => ?_⟩
            rw [mem_support_bind_iff] at hstep
            obtain ⟨value, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure]
            exact List.prefix_append _ _
          | cons head rest =>
            rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape head
              rest leftRecord rightRecord hfresh hleft hright]
            refine ⟨by simp, fun step hstep => ?_⟩
            rw [support_pure, Set.mem_singleton_iff] at hstep
            rw [hstep]
            exact List.prefix_append _ _
        · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache (leftTape, rightTape)
            (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2)]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_rfl
    · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache (leftTape, rightTape)
        (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1)]
      refine ⟨by simp, fun step hstep => ?_⟩
      rw [mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact List.prefix_rfl

open scoped Classical in
/-- The tape-reading run never fails. -/
theorem splitTapeRun_neverFails (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState) :
    Pr[⊥ | (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run state] = 0 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact probFailure_bind_eq_zero_iff _ _ |>.mpr
      ⟨(splitTapeRecorder_step leftKeep rightKeep queried state).1,
        fun step _ => ih step.1 step.2⟩

open scoped Classical in
/-- **The target recording only grows.** -/
theorem rightOf_prefix (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState)
    (result : α × SplitTapeState)
    (hmem : result ∈ support ((simulateQ (splitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    rightOf state <+: rightOf result.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    exact List.IsPrefix.trans
      ((splitTapeRecorder_step leftKeep rightKeep queried state).2 step hstep)
      (ih step.1 step.2 result hrest)

open scoped Classical in
/-- Once a target answer has been recorded the recording has already outgrown the length the
selection asks about, and it never shrinks again. -/
theorem probEvent_length_eq_one (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (tapes : List HashOutput × List HashOutput) (leftRecord rightRecord : Record)
    (entry : Bytes × HashOutput) (bound : Nat)
    (hbound : bound < (rightRecord ++ [entry]).length) :
    Pr[fun result : α × SplitTapeState => bound < (rightOf result.2).length |
        (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
          (cache, tapes, (leftRecord, rightRecord ++ [entry]))] = 1 := by
  classical
  refine probEvent_eq_one ⟨splitTapeRun_neverFails leftKeep rightKeep computation _,
    fun result hmem => ?_⟩
  exact lt_of_lt_of_le hbound (rightOf_prefix leftKeep rightKeep computation
    (cache, tapes, (leftRecord, rightRecord ++ [entry])) result hmem).length_le

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Overwriting an unread cell of the target block does not move the selection.** -/
theorem probEvent_length_set (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (index : Nat) (newValue : HashOutput) (cache : QueryCache HashSpec)
      (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr[fun result : α × SplitTapeState =>
          rightRecord.length + index < (rightOf result.2).length |
        (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), (leftRecord, rightRecord))] =
        Pr[fun result : α × SplitTapeState =>
            rightRecord.length + index < (rightOf result.2).length |
          (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape.set index newValue), (leftRecord, rightRecord))] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro index newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, probEvent_pure]
    rfl
  | query_bind queried next ih =>
    intro index newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · simp only [splitTapeRecorder_run_inl, bind_assoc, pure_bind, probEvent_bind_eq_tsum]
      exact tsum_congr fun answer => congrArg _
        (ih answer index newValue cache leftTape rightTape leftRecord rightRecord)
    · by_cases hfresh : cache input = none
      · by_cases hleft : leftKeep input cache
        · -- The left block is read; the target block passes through untouched.
          cases leftTape with
          | nil =>
            simp only [splitTapeRecorder_run_left_nil leftKeep rightKeep input cache _
              leftRecord rightRecord hfresh hleft, bind_assoc, pure_bind,
              probEvent_bind_eq_tsum]
            exact tsum_congr fun answer => congrArg _
              (ih answer index newValue (cache.cacheQuery input answer) [] rightTape
                (leftRecord ++ [(input, answer)]) rightRecord)
          | cons head rest =>
            simp only [splitTapeRecorder_run_left_cons leftKeep rightKeep input cache head rest
              _ leftRecord rightRecord hfresh hleft, pure_bind]
            exact ih head index newValue (cache.cacheQuery input head) rest rightTape
              (leftRecord ++ [(input, head)]) rightRecord
        · by_cases hright : rightKeep input cache
          · -- The target block is read.
            cases rightTape with
            | nil => simp only [List.set_nil]
            | cons head rest =>
              cases index with
              | zero =>
                -- This is the cell being overwritten; the selection has already happened.
                simp only [List.set_cons_zero,
                  splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape _ _
                    leftRecord rightRecord hfresh hleft hright, pure_bind, Nat.add_zero]
                rw [probEvent_length_eq_one leftKeep rightKeep (next head)
                    (cache.cacheQuery input head) (leftTape, rest) leftRecord rightRecord
                    (input, head) rightRecord.length (by simp),
                  probEvent_length_eq_one leftKeep rightKeep (next newValue)
                    (cache.cacheQuery input newValue) (leftTape, rest) leftRecord rightRecord
                    (input, newValue) rightRecord.length (by simp)]
              | succ remaining =>
                -- The cell is further on, so this step is the same on both sides.
                simp only [List.set_cons_succ,
                  splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape head
                    _ leftRecord rightRecord hfresh hleft hright, pure_bind]
                have hlength : rightRecord.length + (remaining + 1) =
                    (rightRecord ++ [(input, head)]).length + remaining := by
                  simp only [List.length_append, List.length_cons, List.length_nil]
                  omega
                rw [hlength]
                exact ih head remaining newValue (cache.cacheQuery input head) leftTape rest
                  leftRecord (rightRecord ++ [(input, head)])
          · -- Neither block is read.
            simp only [splitTapeRecorder_run_other leftKeep rightKeep input cache _
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind, probEvent_bind_eq_tsum]
            exact tsum_congr fun step => congrArg _
              (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)
      · -- A cache hit reads neither block.
        simp only [splitTapeRecorder_run_other leftKeep rightKeep input cache _
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind, probEvent_bind_eq_tsum]
        exact tsum_congr fun step => congrArg _
          (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)

/-! ## Resampling one cell of the target block

The charge on one cell is the leave-one-out step of `ForsLeaveOneOut.selected_local_hit_le`,
moved to the run. Three things make it go through, and each is proved above rather than assumed:
the disclosures sit on the *other* block, so overwriting a target cell cannot move them; the
cell's own value is what the coverage test reads, so overwriting it replaces that value by a
fresh one; and the selection does not see the cell, which is `probEvent_length_set`.

What comes out is the per-cell factor the expectation form needs: the charge on cell `index` is
the probability that the run *got that far*, times the rate — and summing those probabilities
over the cells is an expected recording length, not a block length. -/

/-- **Overwriting one cell of a block with a fresh draw is drawing the block.** -/
theorem evalDist_padding_set {γ : Type} :
    ∀ (length index : Nat), index < length →
      ∀ (continuation : List HashOutput → ProbComp γ),
        𝒟[padding length >>= continuation] =
          𝒟[padding length >>= fun tape =>
              ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
                continuation (tape.set index value)] := by
  intro length
  induction length with
  | zero => intro index hindex; exact absurd hindex (by omega)
  | succ remaining ih =>
    intro index hindex continuation
    cases index with
    | zero =>
      simp only [padding_succ_bind, List.set_cons_zero]
      refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_comm _ (padding remaining)
        fun value rest => continuation (value :: rest)) ?_
      exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ HashOutput : ProbComp HashOutput) (by simp) _).symm
    | succ smaller =>
      simp only [padding_succ_bind, List.set_cons_succ]
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun head => ?_
      exact ih smaller (by omega) fun rest => continuation (head :: rest)

/-- A cell read back after it was overwritten is the value it was overwritten with. -/
theorem eq_of_getElem?_set (tape : List HashOutput) (index : Nat) (value other : HashOutput)
    (hread : (tape.set index value)[index]? = some other) : other = value := by
  by_cases hlt : index < tape.length
  · rw [List.getElem?_set_self (by simpa using hlt)] at hread
    exact (Option.some_inj.mp hread).symm
  · rw [List.getElem?_eq_none (by simpa using Nat.not_lt.mp hlt)] at hread
    exact absurd hread (by simp)

open scoped Classical in
/-- A constant conjunct factors out of an event. -/
theorem probEvent_const_and {γ : Type} (run : ProbComp γ) (constant : Prop)
    (event : γ → Prop) :
    Pr[fun value => constant ∧ event value | run] =
      if constant then Pr[event | run] else 0 := by
  classical
  by_cases hconstant : constant
  · rw [if_pos hconstant]
    exact probEvent_congr' (fun _ _ => ⟨fun h => h.2, fun h => ⟨hconstant, h⟩⟩) rfl
  · rw [if_neg hconstant]
    exact probEvent_eq_zero fun _ _ h => hconstant h.1

/-- The whole run, with the two blocks it read kept beside its result. -/
noncomputable def blockRun (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftLength rightLength : Nat) :
    ProbComp ((List HashOutput × List HashOutput) × (α × SplitTapeState)) :=
  padding leftLength >>= fun leftTape =>
    padding rightLength >>= fun rightTape =>
      (fun result => ((leftTape, rightTape), result)) <$>
        (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), ([], []))

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The charge on one target cell.** A run whose target recording reaches cell `index`, whose
disclosing block is good, and whose cell `index` is hit by that block, costs the probability of
reaching the cell times the rate — not the rate outright. The weight is what averaging destroys
and what this keeps. -/
theorem prob_selected_hit_le (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftLength rightLength index : Nat) (hindex : index < rightLength)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate) :
    Pr[fun outcome => index < (rightOf outcome.2.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
        blockRun leftKeep rightKeep computation cache leftLength rightLength] ≤
      Pr[fun outcome => index < (rightOf outcome.2.2).length |
        blockRun leftKeep rightKeep computation cache leftLength rightLength] * rate := by
  classical
  set target : List HashOutput → List HashOutput → ℝ≥0∞ := fun leftTape rightTape =>
    Pr[fun result : α × SplitTapeState => index < (rightOf result.2).length |
      (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), ([], []))] with htarget
  -- The selection alone, with the blocks forgotten.
  have hright : Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState) =>
        index < (rightOf outcome.2.2).length |
      blockRun leftKeep rightKeep computation cache leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] * target leftTape rightTape := by
    rw [blockRun, probEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [probEvent_map]
    rfl
  -- The charged event, after one cell of the target block is redrawn.
  have hleft : Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState) =>
        index < (rightOf outcome.2.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
      blockRun leftKeep rightKeep computation cache leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] *
          ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
            Pr[fun result : α × SplitTapeState =>
                index < (rightOf result.2).length ∧ goodBlock leftTape ∧
                  ∃ other, (rightTape.set index value)[index]? = some other ∧
                    hit leftTape other |
              (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
                (cache, (leftTape, rightTape.set index value), ([], []))] := by
    rw [blockRun]
    rw [probEvent_congr' (fun _ _ => Iff.rfl)
      (OracleComp.DeferredSampling.evalDist_bind_congr_left (padding leftLength) _ _
        fun leftTape => evalDist_padding_set rightLength index hindex
          fun rightTape => (fun result => ((leftTape, rightTape), result)) <$>
            (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
              (cache, (leftTape, rightTape), ([], [])))]
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun value => congrArg _ ?_
    rw [probEvent_map]
    rfl
  rw [hleft, hright, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun leftTape => ?_
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun rightTape => ?_)
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  -- The cell's own draw is all that is left to charge.
  calc ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
        Pr[fun result : α × SplitTapeState =>
            index < (rightOf result.2).length ∧ goodBlock leftTape ∧
              ∃ other, (rightTape.set index value)[index]? = some other ∧ hit leftTape other |
          (simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape.set index value), ([], []))]
      ≤ ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if goodBlock leftTape ∧ hit leftTape value then target leftTape rightTape else 0) := by
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        refine le_trans (probEvent_mono (q := fun result : α × SplitTapeState =>
          (goodBlock leftTape ∧ hit leftTape value) ∧
            index < (rightOf result.2).length) ?_) ?_
        · rintro result - ⟨hselected, hgood, other, hread, hhit⟩
          exact ⟨⟨hgood, (eq_of_getElem?_set rightTape index value other hread) ▸ hhit⟩,
            hselected⟩
        · rw [probEvent_const_and]
          by_cases hcase : goodBlock leftTape ∧ hit leftTape value
          · rw [if_pos hcase, if_pos hcase, htarget]
            have hcausal := probEvent_length_set leftKeep rightKeep computation index value
              cache leftTape rightTape [] []
            simp only [List.length_nil, Nat.zero_add] at hcausal
            exact le_of_eq hcausal.symm
          · rw [if_neg hcase, if_neg hcase]
    _ ≤ target leftTape rightTape * rate := by
        by_cases hgood : goodBlock leftTape
        · simp only [hgood, true_and]
          calc ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if hit leftTape value then target leftTape rightTape else 0)
              = (∑' value, if hit leftTape value then
                  Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) *
                  target leftTape rightTape := by
                rw [← ENNReal.tsum_mul_right]
                refine tsum_congr fun value => ?_
                by_cases hhit : hit leftTape value <;> simp [hhit]
            _ ≤ rate * target leftTape rightTape := by
                rw [← probEvent_eq_tsum_ite]
                exact mul_le_mul' (hrate leftTape hgood) le_rfl
            _ = _ := mul_comm _ _
        · simp [hgood]

/-! ## The charge over all the cells

Summing the per-cell charge is where the expectation appears. Each cell contributes the
probability that the run reached it, and `∑ index, Pr[reached index]` is the expected number of
cells reached — the expected length of the target recording, which is the observable the budget
speaks about. Nothing here needs the recording to be short; the block length bounds the sum only
in the sense that a run cannot reach past the block, and that is a cap on the *count*, not on
the charge. -/

/-- A finite sum and a `tsum` over `ℝ≥0∞` may be exchanged. -/
theorem sum_tsum_comm {Index Result : Type} [DecidableEq Index] (indices : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ indices, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ indices, summand index result := by
  refine Finset.induction_on indices ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    refine tsum_congr fun result => ?_
    rw [Finset.sum_insert hhead]

/-- The sum of the per-cell selection probabilities is an expected recording length. -/
theorem sum_prob_selected_le_expected
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftLength rightLength : Nat) :
    (∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState) =>
            index.val < (rightOf outcome.2.2).length |
          blockRun leftKeep rightKeep computation cache leftLength rightLength]) ≤
      ∑' outcome, Pr[= outcome |
          blockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState) =>
            index.val < (rightOf outcome.2.2).length |
          blockRun leftKeep rightKeep computation cache leftLength rightLength]
      = ∑ index : Fin rightLength, ∑' outcome,
          (if index.val < (rightOf outcome.2.2).length then
            Pr[= outcome | blockRun leftKeep rightKeep computation cache leftLength rightLength]
          else 0) :=
        Finset.sum_congr rfl fun index _ => probEvent_eq_tsum_ite _ _
    _ = ∑' outcome, ∑ index : Fin rightLength,
          (if index.val < (rightOf outcome.2.2).length then
            Pr[= outcome | blockRun leftKeep rightKeep computation cache leftLength rightLength]
          else 0) := sum_tsum_comm Finset.univ _
    _ ≤ ∑' outcome, Pr[= outcome |
            blockRun leftKeep rightKeep computation cache leftLength rightLength] *
          (((rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun outcome => ?_
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
          mul_comm]
        refine mul_le_mul' le_rfl (Nat.cast_le.mpr ?_)
        have hinject := Finset.card_le_card_of_injOn (fun index : Fin rightLength => index.val)
          (s := Finset.univ.filter
            (fun index : Fin rightLength => index.val < (rightOf outcome.2.2).length))
          (t := Finset.range (rightOf outcome.2.2).length)
          (fun index hindex => Finset.mem_range.mpr (by simpa using hindex))
          (fun left _ right _ hvalue => Fin.val_injective hvalue)
        simpa using hinject

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The coverage charge, as an expectation.** A run whose disclosing block is good pays, for
the event that some cell of its target recording is hit by that block, its *expected* recording
length times the rate — never the block length.

This is the statement the two-class bound needs and the one a fixed-limit charge cannot be
averaged into. The weight the averaging destroys is kept by `prob_selected_hit_le`, one factor
per cell, and summed here. -/
theorem prob_exists_hit_le_expected
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftLength rightLength : Nat)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState) =>
          ∃ index : Fin rightLength, index.val < (rightOf outcome.2.2).length ∧
            goodBlock outcome.1.1 ∧
            ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value |
        blockRun leftKeep rightKeep computation cache leftLength rightLength] ≤
      (∑' outcome, Pr[= outcome |
          blockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((rightOf outcome.2.2).length : Nat) : ℝ≥0∞)) * rate := by
  classical
  refine le_trans (probEvent_mono (q := fun outcome => ∃ index ∈ (Finset.univ :
      Finset (Fin rightLength)), index.val < (rightOf outcome.2.2).length ∧
      goodBlock outcome.1.1 ∧
      ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value)
    fun outcome _ hhit => by
      obtain ⟨index, hindex⟩ := hhit
      exact ⟨index, Finset.mem_univ index, hindex⟩) ?_
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_selected_hit_le leftKeep rightKeep computation cache leftLength rightLength index.val
      index.isLt goodBlock hit rate hrate) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul' (sum_prob_selected_le_expected leftKeep rightKeep computation cache
    leftLength rightLength) le_rfl

/-! ## The recording is the block, cell for cell

The charge is stated at cell `index` of the target *block*, and the game's event is about the
`index`-th entry of the target *recording*. They are the same answer: the recorder takes each
fresh target answer off the head of the block, in order, so the recording's answers are the
block's cells until the block runs out. Past that the recorder draws for itself and the two
part company, which is why the agreement is claimed only where the block still has a cell. -/

/-- A prefix decides the cells it covers. -/
theorem getElem?_of_prefix {β : Type} {short long : List β} (hprefix : short <+: long)
    (index : Nat) (hindex : index < short.length) : long[index]? = short[index]? := by
  obtain ⟨extra, hextra⟩ := hprefix
  rw [← hextra, List.getElem?_append_left hindex]

open scoped Classical in
/-- **Each recorded target answer is the block cell it was read from.** -/
theorem rightOf_getElem? (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (result : α × SplitTapeState),
      result ∈ support ((simulateQ (splitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord))) →
      ∀ index : Nat, rightRecord.length + index < (rightOf result.2).length →
        index < rightTape.length →
        ((rightOf result.2)[rightRecord.length + index]?).map Prod.snd = rightTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord result hmem index hreached _
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at hreached
    exact absurd hreached (by simp [rightOf])
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord result hmem index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | input
    · rw [splitTapeRecorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ result hrest index hreached hcell
    · by_cases hfresh : cache input = none
      · by_cases hleft : leftKeep input cache
        · -- The left block is read; the target block and recording are untouched.
          cases leftTape with
          | nil =>
            rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input cache rightTape
              leftRecord rightRecord hfresh hleft, mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input cache head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
        · by_cases hright : rightKeep input cache
          · cases rightTape with
            | nil => exact absurd hcell (by simp)
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              cases index with
              | zero =>
                -- This cell is the one just read, and the recording keeps it.
                have hprefix := rightOf_prefix leftKeep rightKeep (next head)
                  (cache.cacheQuery input head, (leftTape, rest),
                    (leftRecord, rightRecord ++ [(input, head)])) result hrest
                rw [Nat.add_zero]
                rw [getElem?_of_prefix hprefix rightRecord.length (by simp [rightOf])]
                simp [rightOf]
              | succ smaller =>
                have hstep' := ih head (cache.cacheQuery input head) leftTape rest leftRecord
                  (rightRecord ++ [(input, head)]) result hrest smaller
                  (by simpa using (by omega : rightRecord.length + 1 + smaller <
                    (rightOf result.2).length))
                  (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hcell))
                rw [show rightRecord.length + (smaller + 1) =
                    (rightRecord ++ [(input, head)]).length + smaller from by simp; omega]
                rw [hstep']
                simp
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ result hrest index hreached hcell

end SlhDsaSecurity.TapeFactor

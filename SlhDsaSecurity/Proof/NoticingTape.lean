import SlhDsaSecurity.Proof.TapeFactor

/-!
# The tape factorisation at the recorder that notices

`TapeFactor.evalDist_splitTapeRun` factorises the two-recording run through two blocks drawn in
advance, at `RecorderView.recorderOf`. The carrier's repair runs
`RecorderView.noticingRecorderOf` instead — the same oracle at a state that has been told about
the query, so that a filing test may read something a cache hit would otherwise hide. This file
is that factorisation at the repaired recorder.

**It is the same induction, and that is the finding.** `noticingRecorderOf` is *defined* as
`recorderOf` run at the noticed carrier, so every step of the proof below is the corresponding
step of `evalDist_splitTapeRun` with `cache` replaced by `CacheView.onQuery cache input`. The
notice does not touch the cache (`RecorderView.cacheOf_onQuery`), so the freshness guard is
unmoved; what moves is only *which state the two tests are read at*, and the tests were already
arbitrary predicates of the state. Nothing about the repair makes the factorisation harder.

**What this does not change.** Not the rate, not what is summed, and not the block lengths: the
statement is the same equality of laws, still unconditional in `leftLength` and `rightLength`,
so everything downstream of it — the leave-one-out charge, the expectation form, the two cell
correspondences — applies verbatim with `noticingSplitTapeRecorder` in place of
`splitTapeRecorder`.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.NoticingTape

open DigestTape TapeFactor RecorderView

variable {σ : Type} [CacheView σ]

/-- **The two-headed tape recorder, told about every query.** The notice is applied to the
carrier before the step, exactly as `RecorderView.noticingRecorderOf` applies it before
`recorderOf`'s; the two blocks and the two recordings ride through untouched. -/
noncomputable def noticingSplitTapeRecorder (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (SplitTapeState σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state
    | Sum.inr input =>
        ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
          (CacheView.onQuery state.1 input, state.2)

theorem noticingSplitTapeRecorder_run_inl (leftKeep rightKeep : Bytes → σ → Prop)
    (coin : unifSpec.Domain) (state : SplitTapeState σ) :
    ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state := rfl

theorem noticingSplitTapeRecorder_run_inr (leftKeep rightKeep : Bytes → σ → Prop)
    (input : Bytes) (state : SplitTapeState σ) :
    ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run state =
      ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (CacheView.onQuery state.1 input, state.2) := rfl

/-- **At a view that notices nothing, it is the tape recorder already in hand.** The mirror of
`RecorderView.noticingRecorderOf_eq`, so this is a widening rather than a fork and everything
proved about `splitTapeRecorder` stands. -/
theorem noticingSplitTapeRecorder_eq (leftKeep rightKeep : Bytes → σ → Prop)
    (hblind : ∀ (view : σ) (input : Bytes), CacheView.onQuery view input = view) :
    noticingSplitTapeRecorder leftKeep rightKeep = splitTapeRecorder leftKeep rightKeep := by
  funext queried state
  rcases queried with coin | input
  · rfl
  · show ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (CacheView.onQuery state.1 input, state.2) = _
    rw [hblind state.1 input]
    rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The repaired two-recording run factorises through two blocks drawn in advance.**
`TapeFactor.evalDist_splitTapeRun` at `RecorderView.noticingRecorderOf`, with the same shape and
the same absence of hypotheses: no constraint on either block length, and none on either test.

A block too short is fallen back from and a block too long has its remainder dropped, exactly as
before — the notice changes neither, because it changes nothing the block is read by. -/
theorem evalDist_noticingSplitTapeRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (leftLength rightLength : Nat) (cache : σ)
      (leftRecord rightRecord : Record),
      𝒟[(simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run
          (cache, leftRecord, rightRecord)] =
        𝒟[padding leftLength >>= fun leftTape =>
            padding rightLength >>= fun rightTape =>
              forgetSplit <$>
                (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
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
    · simp only [noticingRecorderOf_run_inl, noticingSplitTapeRecorder_run_inl,
        RecorderView.recorderOf_run_inl, splitTapeRecorder_run_inl, bind_assoc,
        pure_bind, map_bind]
      refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
        (fun value => ih value leftLength rightLength cache leftRecord rightRecord)) ?_
      exact evalDist_comm_blocks _ leftLength rightLength _
    · -- Every branch below is the cache version's at the **noticed** carrier.
      rw [noticingRecorderOf_run_inr leftKeep rightKeep input (cache, leftRecord, rightRecord)]
      rw [show (fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            forgetSplit <$>
              (((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                  (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= fun step =>
                (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                  (next step.1)).run step.2)) =
          fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            forgetSplit <$>
              (((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                  (CacheView.onQuery cache input, (leftTape, rightTape),
                    (leftRecord, rightRecord)) >>= fun step =>
                (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                  (next step.1)).run step.2) from by
        funext leftTape
        refine congrArg (fun step => padding rightLength >>= step) ?_
        funext rightTape
        rw [noticingSplitTapeRecorder_run_inr]]
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · simp only [splitRecorder_run_left leftKeep rightKeep input noticed leftRecord
            rightRecord hfresh hleft, bind_assoc, pure_bind]
          cases leftLength with
          | zero =>
            simp only [padding_zero_bind,
              splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed _ leftRecord
                rightRecord hfresh hleft, bind_assoc, pure_bind, map_bind]
            refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              (fun value => ih value 0 rightLength (CacheView.update noticed input value)
                (leftRecord ++ [(input, value)]) rightRecord)) ?_
            simp only [padding_zero_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding rightLength) _
          | succ remaining =>
            simp only [padding_succ_bind,
              splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed _ _ _ leftRecord
                rightRecord hfresh hleft, pure_bind]
            exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              fun value => ih value remaining rightLength
                (CacheView.update noticed input value)
                (leftRecord ++ [(input, value)]) rightRecord
        · by_cases hright : rightKeep input noticed
          · simp only [splitRecorder_run_right leftKeep rightKeep input noticed leftRecord
              rightRecord hfresh hleft hright, bind_assoc, pure_bind]
            cases rightLength with
            | zero =>
              simp only [padding_zero_bind,
                splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed _ leftRecord
                  rightRecord hfresh hleft hright, bind_assoc, pure_bind, map_bind]
              refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
                (fun value => ih value leftLength 0 (CacheView.update noticed input value)
                  leftRecord (rightRecord ++ [(input, value)]))) ?_
              simp only [padding_zero_bind]
              exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding leftLength) _
            | succ remaining =>
              simp only [padding_succ_bind,
                splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed _ _ _
                  leftRecord rightRecord hfresh hleft hright, pure_bind]
              refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
                (fun value => ih value leftLength remaining
                  (CacheView.update noticed input value)
                  leftRecord (rightRecord ++ [(input, value)]))) ?_
              exact OracleComp.DeferredSampling.evalDist_bind_comm _ (padding leftLength) _
          · simp only [splitRecorder_run_other leftKeep rightKeep input noticed
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              splitTapeRecorder_run_other leftKeep rightKeep input noticed _
                (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind, map_bind]
            refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              (fun step => ih step.1 leftLength rightLength step.2 leftRecord
                rightRecord)) ?_
            exact evalDist_comm_blocks _ leftLength rightLength _
      · simp only [splitRecorder_run_other leftKeep rightKeep input noticed
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          splitTapeRecorder_run_other leftKeep rightKeep input noticed _
            (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind, map_bind]
        refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
          (fun step => ih step.1 leftLength rightLength step.2 leftRecord rightRecord)) ?_
        exact evalDist_comm_blocks _ leftLength rightLength _

/-! ## The step laws, and everything that follows from them alone

`rightOf` and `leftOf` read the recordings, which the notice does not touch, so
`rightOf (CacheView.onQuery state.1 input, state.2) = rightOf state` holds definitionally. That
is why the three lemmas below are applications of the cache version rather than copies of it:
each is a statement about the recordings, and the notice is invisible to them. -/

open scoped Classical in
/-- **One step of the repaired recorder never fails and appends at most one target entry.** -/
theorem noticingSplitTapeRecorder_step (leftKeep rightKeep : Bytes → σ → Prop)
    (queried : OracleWorld.Domain) (state : SplitTapeState σ) :
    Pr[⊥ | ((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state] = 0 ∧
      ∀ step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state),
        rightOf state <+: rightOf step.2 := by
  classical
  rcases queried with coin | input
  · exact splitTapeRecorder_step leftKeep rightKeep (Sum.inl coin) state
  · rw [noticingSplitTapeRecorder_run_inr]
    exact splitTapeRecorder_step leftKeep rightKeep (Sum.inr input)
      (CacheView.onQuery state.1 input, state.2)

open scoped Classical in
/-- The repaired tape-reading run never fails. -/
theorem noticingSplitTapeRun_neverFails (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState σ) :
    Pr[⊥ | (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run state]
      = 0 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact probFailure_bind_eq_zero_iff _ _ |>.mpr
      ⟨(noticingSplitTapeRecorder_step leftKeep rightKeep queried state).1,
        fun step _ => ih step.1 step.2⟩

open scoped Classical in
/-- **The target recording only grows**, at the repaired recorder. -/
theorem noticingRightOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hmem : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
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
      ((noticingSplitTapeRecorder_step leftKeep rightKeep queried state).2 step hstep)
      (ih step.1 step.2 result hrest)

open scoped Classical in
/-- **The disclosing recording only grows**, at the repaired recorder. -/
theorem noticingLeftOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hmem : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    leftOf state <+: leftOf result.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine List.IsPrefix.trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with coin | input
    · exact leftOf_step leftKeep rightKeep (Sum.inl coin) state step hstep
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      exact leftOf_step leftKeep rightKeep (Sum.inr input)
        (CacheView.onQuery state.1 input, state.2) step hstep

open scoped Classical in
/-- Once a target answer has been recorded the recording has already outgrown the length the
selection asks about, and it never shrinks again. -/
theorem noticingProbEvent_length_eq_one (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (tapes : List HashOutput × List HashOutput) (leftRecord rightRecord : Record)
    (entry : Bytes × HashOutput) (bound : Nat)
    (hbound : bound < (rightRecord ++ [entry]).length) :
    Pr[fun result : α × SplitTapeState σ => bound < (rightOf result.2).length |
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, tapes, (leftRecord, rightRecord ++ [entry]))] = 1 := by
  classical
  refine probEvent_eq_one ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep computation _,
    fun result hmem => ?_⟩
  exact lt_of_lt_of_le hbound (noticingRightOf_prefix leftKeep rightKeep computation
    (cache, tapes, (leftRecord, rightRecord ++ [entry])) result hmem).length_le

/-! ## The selection is still causal

The one step of the cache version whose argument is not bookkeeping, at the repaired recorder.
Its hard case is unchanged and for an unchanged reason: at the step that reads the cell the two
runs genuinely diverge, and the induction does not have to go through, because the event has
already come true there and `noticingRightOf_prefix` keeps it true.

The notice is invisible to this argument. It changes the carrier, and the carrier is what the
two tests read; what the selection reads is the *recording's length*, which the notice does not
touch at all. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Overwriting an unread cell of the target block does not move the selection**, at the
repaired recorder. -/
theorem noticingProbEvent_length_set (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (index : Nat) (newValue : HashOutput) (cache : σ)
      (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr[fun result : α × SplitTapeState σ =>
          rightRecord.length + index < (rightOf result.2).length |
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), (leftRecord, rightRecord))] =
        Pr[fun result : α × SplitTapeState σ =>
            rightRecord.length + index < (rightOf result.2).length |
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
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
    · simp only [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl, bind_assoc,
        pure_bind, probEvent_bind_eq_tsum]
      exact tsum_congr fun answer => congrArg _
        (ih answer index newValue cache leftTape rightTape leftRecord rightRecord)
    · simp only [noticingSplitTapeRecorder_run_inr]
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil =>
            simp only [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed _
              leftRecord rightRecord hfresh hleft, bind_assoc, pure_bind,
              probEvent_bind_eq_tsum]
            exact tsum_congr fun answer => congrArg _
              (ih answer index newValue (CacheView.update noticed input answer) [] rightTape
                (leftRecord ++ [(input, answer)]) rightRecord)
          | cons head rest =>
            simp only [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              _ leftRecord rightRecord hfresh hleft, pure_bind]
            exact ih head index newValue (CacheView.update noticed input head) rest rightTape
              (leftRecord ++ [(input, head)]) rightRecord
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil => simp only [List.set_nil]
            | cons head rest =>
              cases index with
              | zero =>
                simp only [List.set_cons_zero,
                  splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape _ _
                    leftRecord rightRecord hfresh hleft hright, pure_bind, Nat.add_zero]
                rw [noticingProbEvent_length_eq_one leftKeep rightKeep (next head)
                    (CacheView.update noticed input head) (leftTape, rest) leftRecord rightRecord
                    (input, head) rightRecord.length (by simp),
                  noticingProbEvent_length_eq_one leftKeep rightKeep (next newValue)
                    (CacheView.update noticed input newValue) (leftTape, rest) leftRecord
                    rightRecord (input, newValue) rightRecord.length (by simp)]
              | succ remaining =>
                simp only [List.set_cons_succ,
                  splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                    _ leftRecord rightRecord hfresh hleft hright, pure_bind]
                have hlength : rightRecord.length + (remaining + 1) =
                    (rightRecord ++ [(input, head)]).length + remaining := by
                  simp only [List.length_append, List.length_cons, List.length_nil]
                  omega
                rw [hlength]
                exact ih head remaining newValue (CacheView.update noticed input head) leftTape
                  rest leftRecord (rightRecord ++ [(input, head)])
          · simp only [splitTapeRecorder_run_other leftKeep rightKeep input noticed _
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind, probEvent_bind_eq_tsum]
            exact tsum_congr fun step => congrArg _
              (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)
      · simp only [splitTapeRecorder_run_other leftKeep rightKeep input noticed _
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind, probEvent_bind_eq_tsum]
        exact tsum_congr fun step => congrArg _
          (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)

/-! ## The recordings are the blocks, cell for cell

Both correspondences, at the repaired recorder. As in the cache version they are claimed **only
where the block still has a cell**: past that the recorder draws for itself and the two part
company, which is what the two length hypotheses downstream exist to exclude. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Each recorded target answer is the block cell it was read from.** -/
theorem noticingRightOf_getElem? (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (result : α × SplitTapeState σ),
      result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
        computation).run (cache, (leftTape, rightTape), (leftRecord, rightRecord))) →
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
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ result hrest index hreached hcell
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil =>
            rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape
              leftRecord rightRecord hfresh hleft, mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil => exact absurd hcell (by simp)
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              cases index with
              | zero =>
                have hprefix := noticingRightOf_prefix leftKeep rightKeep (next head)
                  (CacheView.update noticed input head, (leftTape, rest),
                    (leftRecord, rightRecord ++ [(input, head)])) result hrest
                rw [Nat.add_zero]
                rw [getElem?_of_prefix hprefix rightRecord.length (by simp [rightOf])]
                simp [rightOf]
              | succ smaller =>
                have hstep' := ih head (CacheView.update noticed input head) leftTape rest
                  leftRecord (rightRecord ++ [(input, head)]) result hrest smaller
                  (by simpa using (by omega : rightRecord.length + 1 + smaller <
                    (rightOf result.2).length))
                  (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hcell))
                rw [show rightRecord.length + (smaller + 1) =
                    (rightRecord ++ [(input, head)]).length + smaller from by simp; omega]
                rw [hstep']
                simp
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ result hrest index hreached hcell

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Each recorded disclosing answer is the block cell it was read from.** -/
theorem noticingLeftOf_getElem? (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (result : α × SplitTapeState σ),
      result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord))) →
      ∀ index : Nat, leftRecord.length + index < (leftOf result.2).length →
        index < leftTape.length →
        ((leftOf result.2)[leftRecord.length + index]?).map Prod.snd = leftTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord result hmem index hreached _
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at hreached
    exact absurd hreached (by simp [leftOf])
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord result hmem index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | input
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ result hrest index hreached hcell
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil => exact absurd hcell (by simp)
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            cases index with
            | zero =>
              have hprefix := noticingLeftOf_prefix leftKeep rightKeep (next head)
                (CacheView.update noticed input head, (rest, rightTape),
                  (leftRecord ++ [(input, head)], rightRecord)) result hrest
              rw [Nat.add_zero, getElem?_of_prefix hprefix leftRecord.length (by simp [leftOf])]
              simp [leftOf]
            | succ smaller =>
              have hstep' := ih head (CacheView.update noticed input head) rest rightTape
                (leftRecord ++ [(input, head)]) rightRecord result hrest smaller
                (by simpa using (by omega : leftRecord.length + 1 + smaller <
                  (leftOf result.2).length))
                (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hcell))
              rw [show leftRecord.length + (smaller + 1) =
                  (leftRecord ++ [(input, head)]).length + smaller from by simp; omega]
              rw [hstep']
              simp
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil =>
              rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape
                leftRecord rightRecord hfresh hleft hright, mem_support_bind_iff] at hstep
              obtain ⟨answer, -, hpure⟩ := hstep
              rw [support_pure, Set.mem_singleton_iff] at hpure
              rw [hpure] at hrest
              exact ih _ _ _ _ _ _ result hrest index hreached hcell
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              exact ih _ _ _ _ _ _ result hrest index hreached hcell
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ result hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ result hrest index hreached hcell

/-! ## The leave-one-out charge, at the repaired recorder

The three lemmas the coverage charge is assembled from. Each is the cache version with its
recorder swapped: none of them inducts over the computation, and the only recorder-specific
thing any of them uses is `noticingProbEvent_length_set` — the causality of the selection, proved
above. The rate, what is summed, and the per-cell factor are untouched, which is what keeps the
margin downstream the same number it was. -/

/-- The whole repaired run, with the two blocks it read kept beside its result. -/
noncomputable def noticingBlockRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) :
    ProbComp ((List HashOutput × List HashOutput) × (α × SplitTapeState σ)) :=
  padding leftLength >>= fun leftTape =>
    padding rightLength >>= fun rightTape =>
      (fun result => ((leftTape, rightTape), result)) <$>
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), ([], []))

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The charge on one target cell**, at the repaired recorder. -/
theorem noticingProb_selected_hit_le (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength index : Nat) (hindex : index < rightLength)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate) :
    Pr[fun outcome => index < (rightOf outcome.2.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
        noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] ≤
      Pr[fun outcome => index < (rightOf outcome.2.2).length |
        noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] * rate := by
  classical
  set target : List HashOutput → List HashOutput → ℝ≥0∞ := fun leftTape rightTape =>
    Pr[fun result : α × SplitTapeState σ => index < (rightOf result.2).length |
      (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), ([], []))] with htarget
  -- The selection alone, with the blocks forgotten.
  have hright : Pr[fun outcome :
        (List HashOutput × List HashOutput) × (α × SplitTapeState σ) =>
        index < (rightOf outcome.2.2).length |
      noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] * target leftTape rightTape := by
    rw [noticingBlockRun, probEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [probEvent_map]
    rfl
  -- The charged event, after one cell of the target block is redrawn.
  have hleft : Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState σ) =>
        index < (rightOf outcome.2.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
      noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] *
          ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
            Pr[fun result : α × SplitTapeState σ =>
                index < (rightOf result.2).length ∧ goodBlock leftTape ∧
                  ∃ other, (rightTape.set index value)[index]? = some other ∧
                    hit leftTape other |
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
                (cache, (leftTape, rightTape.set index value), ([], []))] := by
    rw [noticingBlockRun]
    rw [probEvent_congr' (fun _ _ => Iff.rfl)
      (OracleComp.DeferredSampling.evalDist_bind_congr_left (padding leftLength) _ _
        fun leftTape => evalDist_padding_set rightLength index hindex
          fun rightTape => (fun result => ((leftTape, rightTape), result)) <$>
            (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
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
        Pr[fun result : α × SplitTapeState σ =>
            index < (rightOf result.2).length ∧ goodBlock leftTape ∧
              ∃ other, (rightTape.set index value)[index]? = some other ∧ hit leftTape other |
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape.set index value), ([], []))]
      ≤ ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if goodBlock leftTape ∧ hit leftTape value then target leftTape rightTape else 0) := by
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        refine le_trans (probEvent_mono (q := fun result : α × SplitTapeState σ =>
          (goodBlock leftTape ∧ hit leftTape value) ∧
            index < (rightOf result.2).length) ?_) ?_
        · rintro result - ⟨hselected, hgood, other, hread, hhit⟩
          exact ⟨⟨hgood, (eq_of_getElem?_set rightTape index value other hread) ▸ hhit⟩,
            hselected⟩
        · rw [probEvent_const_and]
          by_cases hcase : goodBlock leftTape ∧ hit leftTape value
          · rw [if_pos hcase, if_pos hcase, htarget]
            have hcausal := noticingProbEvent_length_set leftKeep rightKeep computation index value
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

/-- The sum of the per-cell selection probabilities is an expected recording length. -/
theorem noticingSum_prob_selected_le_expected
    (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) :
    (∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState σ) =>
            index.val < (rightOf outcome.2.2).length |
          noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength]) ≤
      ∑' outcome, Pr[= outcome |
          noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState σ) =>
            index.val < (rightOf outcome.2.2).length |
          noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength]
      = ∑ index : Fin rightLength, ∑' outcome,
          (if index.val < (rightOf outcome.2.2).length then
            Pr[= outcome | noticingBlockRun leftKeep rightKeep computation cache leftLength
              rightLength]
          else 0) :=
        Finset.sum_congr rfl fun index _ => probEvent_eq_tsum_ite _ _
    _ = ∑' outcome, ∑ index : Fin rightLength,
          (if index.val < (rightOf outcome.2.2).length then
            Pr[= outcome | noticingBlockRun leftKeep rightKeep computation cache leftLength
              rightLength]
          else 0) := sum_tsum_comm Finset.univ _
    _ ≤ ∑' outcome, Pr[= outcome |
            noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] *
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
/-- **The coverage charge, as an expectation**, at the repaired recorder. This is what the
carrier's answer run composes with. -/
theorem noticingProb_exists_hit_le_expected
    (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × (α × SplitTapeState σ) =>
          ∃ index : Fin rightLength, index.val < (rightOf outcome.2.2).length ∧
            goodBlock outcome.1.1 ∧
            ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value |
        noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] ≤
      (∑' outcome, Pr[= outcome |
          noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] *
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
    noticingProb_selected_hit_le leftKeep rightKeep computation cache leftLength rightLength
      index.val
      index.isLt goodBlock hit rate hrate) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul' (noticingSum_prob_selected_le_expected leftKeep rightKeep computation cache
    leftLength rightLength) le_rfl

end SlhDsaSecurity.NoticingTape

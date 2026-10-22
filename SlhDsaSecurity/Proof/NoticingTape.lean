import SlhDsaSecurity.Proof.TapeFactor
import SlhDsaSecurity.Proof.CoverageCount

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


/-! ## The charge, with the run a parameter

The three lemmas the coverage charge is assembled from use only four things about the run: that
one cell of the target block may be redrawn, that the run's *selection* of that cell does not
see its value, that a recorded entry is the block cell it came from, and that the whole thing
never fails. Only the second mentions the run at all, and it is the one a new presentation has
to prove.

So they are stated over an arbitrary `run`, with the selection's causality as a hypothesis. The
repaired recorder's instances below supply it from `noticingProbEvent_length_set`; a bracketed
three-stage run supplies it from its own and gets the rest free. **Stating the charge once means
the rate and the index set are written once**, which is the same protection the
blocks-drawn-at-the-top design gives: a second copy is a second place the margin could be spent.
-/

/-- A run with the two blocks it read kept beside its result. -/
noncomputable def blockRunOf {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) :
    ProbComp ((List HashOutput × List HashOutput) × ρ) :=
  padding leftLength >>= fun leftTape =>
    padding rightLength >>= fun rightTape =>
      (fun result => ((leftTape, rightTape), result)) <$> run leftTape rightTape

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The charge on one target cell**, at the repaired recorder. -/
theorem prob_selected_hit_le_of_causal {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength index : Nat) (hindex : index < rightLength)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hcausal : ∀ (leftTape rightTape : List HashOutput) (value : HashOutput),
      Pr[fun z : ρ => index < (rightOfResult z).length |
          run leftTape (rightTape.set index value)] =
        Pr[fun z : ρ => index < (rightOfResult z).length |
          run leftTape rightTape]) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < (rightOfResult outcome.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
        blockRunOf run leftLength rightLength] ≤
      Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < (rightOfResult outcome.2).length |
        blockRunOf run leftLength rightLength] * rate := by
  classical
  set target : List HashOutput → List HashOutput → ℝ≥0∞ := fun leftTape rightTape =>
    Pr[fun result : ρ => index < (rightOfResult result).length |
      run leftTape rightTape] with htarget
  -- The selection alone, with the blocks forgotten.
  have hright : Pr[fun outcome :
        (List HashOutput × List HashOutput) × ρ =>
        index < (rightOfResult outcome.2).length |
      blockRunOf run leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] * target leftTape rightTape := by
    rw [blockRunOf, probEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [probEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [probEvent_map]
    rfl
  -- The charged event, after one cell of the target block is redrawn.
  have hleft : Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
        index < (rightOfResult outcome.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value |
      blockRunOf run leftLength rightLength] =
      ∑' leftTape, Pr[= leftTape | padding leftLength] *
        ∑' rightTape, Pr[= rightTape | padding rightLength] *
          ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
            Pr[fun result : ρ =>
                index < (rightOfResult result).length ∧ goodBlock leftTape ∧
                  ∃ other, (rightTape.set index value)[index]? = some other ∧
                    hit leftTape other |
              run leftTape (rightTape.set index value)] := by
    rw [blockRunOf]
    rw [probEvent_congr' (fun _ _ => Iff.rfl)
      (OracleComp.DeferredSampling.evalDist_bind_congr_left (padding leftLength) _ _
        fun leftTape => evalDist_padding_set rightLength index hindex
          fun rightTape => (fun result => ((leftTape, rightTape), result)) <$>
            run leftTape rightTape)]
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
        Pr[fun result : ρ =>
            index < (rightOfResult result).length ∧ goodBlock leftTape ∧
              ∃ other, (rightTape.set index value)[index]? = some other ∧ hit leftTape other |
          run leftTape (rightTape.set index value)]
      ≤ ∑' value, Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if goodBlock leftTape ∧ hit leftTape value then target leftTape rightTape else 0) := by
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        refine le_trans (probEvent_mono (q := fun result : ρ =>
          (goodBlock leftTape ∧ hit leftTape value) ∧
            index < (rightOfResult result).length) ?_) ?_
        · rintro result - ⟨hselected, hgood, other, hread, hhit⟩
          exact ⟨⟨hgood, (eq_of_getElem?_set rightTape index value other hread) ▸ hhit⟩,
            hselected⟩
        · rw [probEvent_const_and]
          by_cases hcase : goodBlock leftTape ∧ hit leftTape value
          · rw [if_pos hcase, if_pos hcase, htarget]
            exact le_of_eq (hcausal leftTape rightTape value)
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
theorem sum_prob_selected_le_expected_of {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength : Nat) :
    (∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
            index.val < (rightOfResult outcome.2).length |
          blockRunOf run leftLength rightLength]) ≤
      ∑' outcome, Pr[= outcome |
          blockRunOf run leftLength rightLength] *
        (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : Fin rightLength,
        Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
            index.val < (rightOfResult outcome.2).length |
          blockRunOf run leftLength rightLength]
      = ∑ index : Fin rightLength, ∑' outcome,
          (if index.val < (rightOfResult outcome.2).length then
            Pr[= outcome | blockRunOf run leftLength
              rightLength]
          else 0) :=
        Finset.sum_congr rfl fun index _ => probEvent_eq_tsum_ite _ _
    _ = ∑' outcome, ∑ index : Fin rightLength,
          (if index.val < (rightOfResult outcome.2).length then
            Pr[= outcome | blockRunOf run leftLength
              rightLength]
          else 0) := sum_tsum_comm Finset.univ _
    _ ≤ ∑' outcome, Pr[= outcome |
            blockRunOf run leftLength rightLength] *
          (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun outcome => ?_
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
          mul_comm]
        refine mul_le_mul' le_rfl (Nat.cast_le.mpr ?_)
        have hinject := Finset.card_le_card_of_injOn (fun index : Fin rightLength => index.val)
          (s := Finset.univ.filter
            (fun index : Fin rightLength => index.val < (rightOfResult outcome.2).length))
          (t := Finset.range (rightOfResult outcome.2).length)
          (fun index hindex => Finset.mem_range.mpr (by simpa using hindex))
          (fun left _ right _ hvalue => Fin.val_injective hvalue)
        simpa using hinject

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The coverage charge, as an expectation**, at the repaired recorder. This is what the
carrier's answer run composes with. -/
theorem prob_exists_hit_le_expected_of_causal {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength : Nat)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr[fun value => hit leftTape value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hcausal : ∀ (index : Nat) (leftTape rightTape : List HashOutput)
        (value : HashOutput),
      Pr[fun z : ρ => index < (rightOfResult z).length |
          run leftTape (rightTape.set index value)] =
        Pr[fun z : ρ => index < (rightOfResult z).length |
          run leftTape rightTape]) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ =>
          ∃ index : Fin rightLength, index.val < (rightOfResult outcome.2).length ∧
            goodBlock outcome.1.1 ∧
            ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value |
        blockRunOf run leftLength rightLength] ≤
      (∑' outcome, Pr[= outcome |
          blockRunOf run leftLength rightLength] *
        (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) * rate := by
  classical
  refine le_trans (probEvent_mono (q := fun outcome => ∃ index ∈ (Finset.univ :
      Finset (Fin rightLength)), index.val < (rightOfResult outcome.2).length ∧
      goodBlock outcome.1.1 ∧
      ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value)
    fun outcome _ hhit => by
      obtain ⟨index, hindex⟩ := hhit
      exact ⟨index, Finset.mem_univ index, hindex⟩) ?_
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_selected_hit_le_of_causal run rightOfResult leftLength rightLength
      index.val
      index.isLt goodBlock hit rate hrate (hcausal index.val)) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul' (sum_prob_selected_le_expected_of run rightOfResult
    leftLength rightLength) le_rfl

/-! ## The recordings are still invisible

`CoverageCount.recorderOf_eq_rom` says an event about the result and the view's cache has the
same probability under the recorded run as under the shared oracle's — the write-only bridge
the structural term is read across. At the repaired recorder it is the same statement for the
same reason, and the *notice does not move the right-hand side at all*: `cacheOf_onQuery` says
noticing a query leaves the cache alone, so the oracle's run is started and continued at exactly
the cache it was before. Only the carrier under the recording moves, and the event cannot see
the carrier except through its cache. -/


/-! ## The repaired recorder's instances, as applications -/

theorem noticingBlockRun_eq (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : σ) (leftLength rightLength : Nat) :
    noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength =
      blockRunOf (fun leftTape rightTape =>
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), ([], []))) leftLength rightLength := rfl

open scoped Classical in
/-- The causality hypothesis at the repaired recorder, in the shape the charge asks for. -/
theorem noticingCausal (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : σ)
    (index : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput) :
    Pr[fun z : α × SplitTapeState σ => index < (rightOf z.2).length |
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape.set index value), ([], []))] =
      Pr[fun z : α × SplitTapeState σ => index < (rightOf z.2).length |
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, (leftTape, rightTape), ([], []))] := by
  classical
  have h := noticingProbEvent_length_set leftKeep rightKeep computation index value cache
    leftTape rightTape [] []
  simp only [List.length_nil, Nat.zero_add] at h
  exact h.symm

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
  rw [noticingBlockRun_eq]
  exact prob_selected_hit_le_of_causal
    (fun leftTape rightTape =>
      (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), ([], []))) (fun z => rightOf z.2)
    leftLength rightLength index
    hindex goodBlock hit rate hrate
    (noticingCausal leftKeep rightKeep computation cache index)
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
  rw [noticingBlockRun_eq]
  exact sum_prob_selected_le_expected_of
    (fun leftTape rightTape =>
      (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), ([], []))) (fun z => rightOf z.2) leftLength rightLength
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
  rw [noticingBlockRun_eq]
  exact prob_exists_hit_le_expected_of_causal
    (fun leftTape rightTape =>
      (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), ([], []))) (fun z => rightOf z.2) leftLength rightLength
    goodBlock hit rate hrate
    (noticingCausal leftKeep rightKeep computation cache)
set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The recordings are invisible at the repaired recorder.**
`CoverageCount.recorderOf_eq_rom` at `RecorderView.noticingRecorderOf`. -/
theorem noticingRecorderOf_eq_rom {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ)
    (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result : α × StateOf σ => event (result.1, CacheView.cacheOf result.2.1) |
        (simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run state] =
      Pr[event | (simulateQ KeygenUniform.rom computation).run
        (CacheView.cacheOf state.1)] := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · rw [noticingRecorderOf_run_inl, RecorderView.recorderOf_run_inl, DigestTape.rom_run_inl,
        bind_assoc, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      exact tsum_congr fun value => by rw [ih value state]
    · rw [noticingRecorderOf_run_inr]
      have hview : CacheView.cacheOf (CacheView.onQuery state.1 input) =
          CacheView.cacheOf state.1 := cacheOf_onQuery state.1 input
      cases hcached : CacheView.cacheOf state.1 input with
      | some cached =>
        rw [RecorderView.recorderOf_run_inr_some _ _ input
            (CacheView.onQuery state.1 input, state.2) cached (by rw [hview]; exact hcached),
          CoverageCount.rom_run_inr_some input _ cached hcached]
        simp only [pure_bind]
        simpa only [hview] using ih cached (CacheView.onQuery state.1 input,
          RecorderView.appendedOf leftKeep rightKeep input
            (CacheView.onQuery state.1 input, state.2) cached)
      | none =>
        rw [RecorderView.recorderOf_run_inr_none _ _ input
            (CacheView.onQuery state.1 input, state.2) (by rw [hview]; exact hcached),
          CoverageCount.rom_run_inr_none input _ hcached]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        refine tsum_congr fun answer => ?_
        rw [← hview, ← CacheView.cache_update (CacheView.onQuery state.1 input) input answer]
        exact congrArg _ (ih answer
          (CacheView.update (CacheView.onQuery state.1 input) input answer,
            RecorderView.appendedOf leftKeep rightKeep input
              (CacheView.onQuery state.1 input, state.2) answer))

/-! ## The factorisation with a continuation, which is what composes

`evalDist_noticingSplitTapeRun` factorises **one** run. The carrier's tail is three runs, and
the middle one contains a *nested* run — the signer's own queries, simulated through the same
handler between two bracket points. Chaining the one-run statement does not work, and the reason
is worth stating because it is what forces this generalisation: after a run has consumed part of
a block, what is left is a block of a length the run itself chose, so the next stage cannot draw
a fresh one and cannot be handed the remainder as data either.

The fix is to make the continuation a parameter on both sides and to demand of it **exactly what
the conclusion gives**: that it factorises against freshly drawn blocks, at every pair of
lengths. The statement then composes with itself — the hypothesis of the composite is the
conclusion of the tail — and the `pure` case is the hypothesis applied once rather than a
dropped block.

**Blocks are drawn once, at the top.** That is not an optimisation. Three stages each drawing
their own block would give the per-cell charge three index sets instead of one, and the counting
step in `noticingSum_prob_selected_le_expected` would be summing over a different thing. Drawn
once and threaded, the index set stays `Fin rightLength` over one block and the rate stays the
per-cell one. The design cannot spend the concentration margin, rather than being shown not to.
-/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The tape factorisation with an arbitrary continuation on each side.** The hypothesis is
the conclusion's own shape at the continuation, which is what lets this be used at a nested run:
the outer induction supplies `hafter` and this supplies the inner run. -/
theorem evalDist_noticingSplitTapeRun_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (handlerAfter : α × StateOf σ → ProbComp γ)
    (tapeAfter : α × SplitTapeState σ → ProbComp γ)
    (hafter : ∀ (leftLength rightLength : Nat) (z : α × StateOf σ),
      𝒟[handlerAfter z] =
        𝒟[padding leftLength >>= fun leftTape => padding rightLength >>= fun rightTape =>
            tapeAfter (z.1, (z.2.1, (leftTape, rightTape), z.2.2))]) :
    ∀ (leftLength rightLength : Nat) (cache : σ) (leftRecord rightRecord : Record),
      𝒟[(simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run
          (cache, leftRecord, rightRecord) >>= handlerAfter] =
        𝒟[padding leftLength >>= fun leftTape =>
            padding rightLength >>= fun rightTape =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
                  (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= tapeAfter] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hafter leftLength rightLength (value, (cache, leftRecord, rightRecord))
  | query_bind queried next ih =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with coin | input
    · simp only [noticingRecorderOf_run_inl, noticingSplitTapeRecorder_run_inl,
        RecorderView.recorderOf_run_inl, splitTapeRecorder_run_inl, bind_assoc, pure_bind]
      refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
        (fun value => ih value leftLength rightLength cache leftRecord rightRecord)) ?_
      exact evalDist_comm_blocks _ leftLength rightLength _
    · rw [noticingRecorderOf_run_inr leftKeep rightKeep input (cache, leftRecord, rightRecord)]
      rw [show (fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= fun step =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                (next step.1)).run step.2 >>= tapeAfter) =
          fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                (CacheView.onQuery cache input, (leftTape, rightTape),
                  (leftRecord, rightRecord)) >>= fun step =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                (next step.1)).run step.2 >>= tapeAfter from by
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
                rightRecord hfresh hleft, bind_assoc, pure_bind]
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
                  rightRecord hfresh hleft hright, bind_assoc, pure_bind]
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
              bind_assoc, pure_bind]
            refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
              (fun step => ih step.1 leftLength rightLength step.2 leftRecord
                rightRecord)) ?_
            exact evalDist_comm_blocks _ leftLength rightLength _
      · simp only [splitRecorder_run_other leftKeep rightKeep input noticed
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          splitTapeRecorder_run_other leftKeep rightKeep input noticed _
            (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind]
        refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
          (fun step => ih step.1 leftLength rightLength step.2 leftRecord rightRecord)) ?_
        exact evalDist_comm_blocks _ leftLength rightLength _

/-- **The one-run factorisation is this one at the forgetting continuation.** So the
generalisation is a widening and not a fork: `evalDist_noticingSplitTapeRun` is recovered by
taking the continuation to be `pure` after `forgetSplit`, whose hypothesis is the dropped
block. -/
theorem evalDist_noticingSplitTapeRun_of_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α)
    (leftLength rightLength : Nat) (cache : σ) (leftRecord rightRecord : Record) :
    𝒟[(simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run
        (cache, leftRecord, rightRecord)] =
      𝒟[padding leftLength >>= fun leftTape =>
          padding rightLength >>= fun rightTape =>
            forgetSplit <$>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
                (cache, (leftTape, rightTape), (leftRecord, rightRecord))] := by
  classical
  have hbind := evalDist_noticingSplitTapeRun_cont leftKeep rightKeep computation
    (fun z => (pure z : ProbComp (α × StateOf σ)))
    (fun z => (pure (forgetSplit z) : ProbComp (α × StateOf σ)))
    (fun lL rL z => by
      have hconst : ∀ leftTape rightTape : List HashOutput,
          (pure (forgetSplit (z.1, (z.2.1, (leftTape, rightTape), z.2.2))) :
            ProbComp (α × StateOf σ)) = pure z := fun _ _ => rfl
      simp only [hconst]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding lL)
          (padding_neverFails lL),
        OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding rL)
          (padding_neverFails rL)])
    leftLength rightLength cache leftRecord rightRecord
  simpa only [bind_pure, map_eq_bind_pure_comp, Function.comp_def] using hbind

/-! ## The selection's causality, with a continuation

`noticingProbEvent_length_set` says a single run's selection of a target cell does not see that
cell's value. The bracketed tail is three runs, and chaining the single-run statement hits the
same obstruction the factorisation did: after the first stage the two sides are in different
states, so the second stage's probability is not the same object on both sides.

The repair is the same one, and that it is the same one is the point. The continuation is a
parameter, and what is asked of it is **the conclusion's own shape** — that its selection does
not see the cell either — plus two facts that compose by themselves: it never fails, and it
never shortens the target recording. The `pure` case is then the continuation's own causality
rather than a termination, and the step that *reads* the cell is settled on both sides by the
recording already being long enough, exactly as before.
-/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Once the recording is long enough the whole rest of the run keeps it so.** The
continuation form of `noticingProbEvent_length_eq_one`: the run only grows the recording and the
continuation only grows it further, and neither can fail. -/
theorem probEvent_length_eq_one_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ) (finalRight : γ → Record)
    (hgrow : ∀ (z : α × SplitTapeState σ) (w : γ), w ∈ support (after z) ->
      (rightOf z.2).length ≤ (finalRight w).length)
    (hfail : ∀ z, Pr[⊥ | after z] = 0)
    (cache : σ) (tapes : List HashOutput × List HashOutput)
    (leftRecord rightRecord : Record) (entry : Bytes × HashOutput) (bound : Nat)
    (hbound : bound < (rightRecord ++ [entry]).length) :
    Pr[fun w => bound < (finalRight w).length |
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, tapes, (leftRecord, rightRecord ++ [entry])) >>= after] = 1 := by
  classical
  refine probEvent_eq_one ?_
  constructor
  · refine probFailure_bind_eq_zero_iff _ _ |>.mpr
      ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep computation _,
        fun z _ => hfail z⟩
  · intro w hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hafterMem⟩ := hw
    have hprefix := noticingRightOf_prefix leftKeep rightKeep computation
      (cache, tapes, (leftRecord, rightRecord ++ [entry])) z hz
    exact lt_of_lt_of_le (lt_of_lt_of_le hbound hprefix.length_le) (hgrow z w hafterMem)

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Overwriting an unread cell does not move the selection**, with a continuation. The
hypothesis `hafter` is this statement at the continuation, so the conclusion composes with
itself across the stages of a bracketed run. -/
theorem probEvent_length_set_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ) (finalRight : γ → Record)
    (hgrow : ∀ (z : α × SplitTapeState σ) (w : γ), w ∈ support (after z) ->
      (rightOf z.2).length ≤ (finalRight w).length)
    (hfail : ∀ z, Pr[⊥ | after z] = 0)
    (hafter : ∀ (index : Nat) (newValue : HashOutput)
        (z : α × SplitTapeState σ),
      Pr[fun w => (rightOf z.2).length + index < (finalRight w).length | after z] =
        Pr[fun w => (rightOf z.2).length + index < (finalRight w).length |
          after (z.1, (z.2.1, (z.2.2.1.1, z.2.2.1.2.set index newValue), z.2.2.2))]) :
    ∀ (index : Nat) (newValue : HashOutput) (cache : σ)
      (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr[fun w => rightRecord.length + index < (finalRight w).length |
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after] =
        Pr[fun w => rightRecord.length + index < (finalRight w).length |
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape.set index newValue), (leftRecord, rightRecord))
              >>= after] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro index newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hafter index newValue
      (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord)))
  | query_bind queried next ih =>
    intro index newValue cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with coin | input
    · simp only [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl, bind_assoc,
        pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      exact tsum_congr fun answer => congrArg _
        (ih answer index newValue cache leftTape rightTape leftRecord rightRecord)
    · simp only [noticingSplitTapeRecorder_run_inr]
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil =>
            simp only [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed _
              leftRecord rightRecord hfresh hleft, bind_assoc, pure_bind]
            rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
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
                rw [probEvent_length_eq_one_cont leftKeep rightKeep (next head) after finalRight
                    hgrow hfail (CacheView.update noticed input head) (leftTape, rest) leftRecord
                    rightRecord (input, head) rightRecord.length (by simp),
                  probEvent_length_eq_one_cont leftKeep rightKeep (next newValue) after
                    finalRight hgrow hfail (CacheView.update noticed input newValue)
                    (leftTape, rest) leftRecord rightRecord (input, newValue)
                    rightRecord.length (by simp)]
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
              bind_assoc, pure_bind]
            rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
            exact tsum_congr fun step => congrArg _
              (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)
      · simp only [splitTapeRecorder_run_other leftKeep rightKeep input noticed _
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        exact tsum_congr fun step => congrArg _
          (ih step.1 index newValue step.2 leftTape rightTape leftRecord rightRecord)

/-! ## The cell correspondence, with a continuation — and the invariant it retires

The correspondence relates the **final** recording at offset `rightRecord.length + index` to the
**starting** block at `index`. Chaining the single-run form across stages looks as though it
needs a new invariant — that the block shortens by exactly as much as the recording grows —
because otherwise a later stage's block index does not line up with the original one. That
statement is true, obvious, and load-bearing, which is the most dangerous combination; and it is
not needed.

**The continuation form removes the need for it, because each layer speaks of its own offsets.**
The hypothesis is the conclusion at the continuation's *own* starting recording and block, so no
global index arithmetic ever appears: the outer layer relates the original offsets to the
intermediate ones, the inner layer relates the intermediate ones to the final, and nothing has to
count how many cells the first stage ate. That is the fifth time the continuation shape has paid,
and the first time it has retired a lemma rather than enabled one.
-/

/-- The unread remainder of the target block. -/
def rightTapeOf (state : SplitTapeState σ) : List HashOutput := state.2.1.2

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Each recorded target answer is the block cell it was read from**, with a continuation. -/
theorem rightOf_getElem?_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ)
    (finalRight : γ → Record)
    (hprefix : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → rightOf z.2 <+: finalRight w)
    (hafter : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → ∀ index : Nat,
        (rightOf z.2).length + index < (finalRight w).length ->
        index < (rightTapeOf z.2).length ->
          ((finalRight w)[(rightOf z.2).length + index]?).map Prod.snd =
            (rightTapeOf z.2)[index]?) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (w : γ),
      w ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after) ->
      ∀ index : Nat, rightRecord.length + index < (finalRight w).length ->
        index < rightTape.length ->
        ((finalRight w)[rightRecord.length + index]?).map Prod.snd = rightTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_pure, StateT.run_pure, pure_bind] at hw
    exact hafter (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord))) w hw index
      hreached hcell
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      mem_support_bind_iff] at hw
    obtain ⟨step, hstep, hrest⟩ := hw
    rcases queried with coin | input
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ w hrest index hreached hcell
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
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
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
                rw [mem_support_bind_iff] at hrest
                obtain ⟨inner, hinner, hw2⟩ := hrest
                have hmid := noticingRightOf_prefix leftKeep rightKeep (next head)
                  (CacheView.update noticed input head, (leftTape, rest),
                    (leftRecord, rightRecord ++ [(input, head)])) inner hinner
                have hall : rightRecord ++ [(input, head)] <+: finalRight w :=
                  List.IsPrefix.trans hmid (hprefix inner w hw2)
                rw [Nat.add_zero]
                rw [getElem?_of_prefix hall rightRecord.length (by simp)]
                simp
              | succ smaller =>
                have hstep' := ih _ _ _ _ _ _ w hrest smaller
                  (by simpa using (by omega : rightRecord.length + 1 + smaller <
                    (finalRight w).length))
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
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ w hrest index hreached hcell

/-- The unread remainder of the disclosing block. -/
def leftTapeOf (state : SplitTapeState σ) : List HashOutput := state.2.1.1

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Each recorded disclosing answer is the block cell it was read from**, with a continuation.
The mirror of `rightOf_getElem?_cont`. The two sides are not one lemma: the recorder's branches
differ in which block they consume and which recording they file, so a side-parameterised
version would have to swap the branch cases rather than abstract them. -/
theorem leftOf_getElem?_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ)
    (finalLeft : γ → Record)
    (hprefix : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → leftOf z.2 <+: finalLeft w)
    (hafter : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → ∀ index : Nat,
        (leftOf z.2).length + index < (finalLeft w).length →
        index < (leftTapeOf z.2).length →
          ((finalLeft w)[(leftOf z.2).length + index]?).map Prod.snd =
            (leftTapeOf z.2)[index]?) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (w : γ),
      w ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after) →
      ∀ index : Nat, leftRecord.length + index < (finalLeft w).length →
        index < leftTape.length →
        ((finalLeft w)[leftRecord.length + index]?).map Prod.snd = leftTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_pure, StateT.run_pure, pure_bind] at hw
    exact hafter (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord))) w hw index
      hreached hcell
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      mem_support_bind_iff] at hw
    obtain ⟨step, hstep, hrest⟩ := hw
    rcases queried with coin | input
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ w hrest index hreached hcell
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
              rw [mem_support_bind_iff] at hrest
              obtain ⟨inner, hinner, hw2⟩ := hrest
              have hmid := noticingLeftOf_prefix leftKeep rightKeep (next head)
                (CacheView.update noticed input head, (rest, rightTape),
                  (leftRecord ++ [(input, head)], rightRecord)) inner hinner
              have hall : leftRecord ++ [(input, head)] <+: finalLeft w :=
                List.IsPrefix.trans hmid (hprefix inner w hw2)
              rw [Nat.add_zero]
              rw [getElem?_of_prefix hall leftRecord.length (by simp)]
              simp
            | succ smaller =>
              have hstep' := ih _ _ _ _ _ _ w hrest smaller
                (by simpa using (by omega : leftRecord.length + 1 + smaller <
                  (finalLeft w).length))
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
              exact ih _ _ _ _ _ _ w hrest index hreached hcell
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              exact ih _ _ _ _ _ _ w hrest index hreached hcell
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ w hrest index hreached hcell

open scoped Classical in
/-- **A run with the blocks beside it never fails, if the run does not.** -/
theorem blockRunOf_tail_neverFails {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (hfail : ∀ leftTape rightTape, Pr[⊥ | run leftTape rightTape] = 0)
    (leftTape : List HashOutput) (rightLength : Nat) :
    Pr[⊥ | padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$> run leftTape rightTape] = 0 := by
  refine probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨padding_neverFails rightLength,
    fun rightTape _ => ?_⟩
  rw [map_eq_bind_pure_comp]
  exact probFailure_bind_eq_zero_iff _ _ |>.mpr
    ⟨hfail leftTape rightTape, fun _ _ => by simp⟩

open scoped Classical in
/-- **The disclosing block's own law, at any run.** An event about the left block alone is an
event about the block draw, which is what lets the concentration bound be read at the blocked
run. Stated over the run so that the repaired recorder and a bracketed three-stage run read one
lemma. -/
theorem prob_leftBlock_of {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (hfail : ∀ leftTape rightTape, Pr[⊥ | run leftTape rightTape] = 0)
    (leftLength rightLength : Nat) (event : List HashOutput → Prop) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × ρ => event outcome.1.1 |
        blockRunOf run leftLength rightLength] =
      Pr[event | padding leftLength] := by
  classical
  rw [blockRunOf, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun leftTape => ?_
  have hshape : ∀ outcome ∈ support (padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$> run leftTape rightTape),
      outcome.1.1 = leftTape := by
    intro outcome hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨rightTape, -, hinner⟩ := hmem
    rw [support_map] at hinner
    obtain ⟨result, -, hbuilt⟩ := hinner
    rw [← hbuilt]
  rw [probEvent_congr' (fun outcome hmem => by rw [hshape outcome hmem]) rfl,
    probEvent_const, blockRunOf_tail_neverFails run hfail leftTape rightLength, tsub_zero]
  split <;> simp

open scoped Classical in
/-- **A supported outcome of a blocked run is a supported run against its own two blocks.** -/
theorem mem_support_blockRunOf {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat)
    (outcome : (List HashOutput × List HashOutput) × ρ)
    (hmem : outcome ∈ support (blockRunOf run leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧
      outcome.1.2 ∈ support (padding rightLength) ∧
        outcome.2 ∈ support (run outcome.1.1 outcome.1.2) := by
  rw [blockRunOf, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleftTape, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hrightTape, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨result, hresult, hshape⟩ := hinner
  rw [← hshape]
  exact ⟨hleftTape, hrightTape, hresult⟩

end SlhDsaSecurity.NoticingTape

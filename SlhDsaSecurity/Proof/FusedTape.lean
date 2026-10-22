import SlhDsaSecurity.Proof.NoticingTape
import SlhDsaSecurity.Proof.PhaseFusion

/-!
# The tape factorisation at the fused handler

`NoticingTape.evalDist_noticingSplitTapeRun_cont` factorises a run of the repaired recorder
with an arbitrary continuation. This file is the same statement for
`PhaseFusion.fuseServing` — the handler the adversary's phase runs under, which takes a signing
request in one step with a bracket on either side.

**There is no second induction over `OracleWorld` here, and that is what the keystone bought.**
`PhaseFusion.fuse` runs `simulateQ outer` on *both* branches — the inner handler lifts a query,
world or signing, into an `OracleComp OracleWorld` and the outer handler simulates it. So every
case of the induction below is one nested run followed by the rest of the phase, which is
exactly the keystone's shape: the nested run is discharged by it, and its hypothesis is this
induction's own hypothesis at the tail.

**The brackets act on the carrier alone**, and that is a choice rather than an accident. A
bracket stated at the whole handler state would need a hypothesis saying it leaves the two
recordings alone, and — once the blocks are in the state — a second saying it leaves those
alone too. Stated at the carrier, both are structural: `onCarrier` and `onCarrierTape` cannot
reach a recording or a block, so the bracket cases need no hypothesis at all. Put the thing an
invariant must not see outside the thing the invariant is about.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.FusedTape

open Security DigestTape TapeFactor NoticingTape RecorderView PhaseFusion

variable {σ : Type} [CacheView σ] {ω : Type} [Monoid ω]

/-- A carrier-level state map, as the recorder's state sees it. -/
def onCarrier (f : σ → σ) (state : StateOf σ) : StateOf σ := (f state.1, state.2)

/-- The same map, as the tape recorder's state sees it. The blocks and the recordings are in
components the map cannot reach. -/
def onCarrierTape (f : σ → σ) (state : SplitTapeState σ) : SplitTapeState σ :=
  (f state.1, state.2)

theorem onCarrier_fst (f : σ → σ) (state : StateOf σ) :
    (onCarrier f state).1 = f state.1 := rfl

theorem onCarrierTape_fst (f : σ → σ) (state : SplitTapeState σ) :
    (onCarrierTape f state).1 = f state.1 := rfl

theorem fuseServing_run_inl {S : Type} (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S) (world : OracleWorld.Domain)
    (state : ω × SigningLog × S) :
    ((fuseServing outer inner before after) (Sum.inl world)).run state =
      (simulateQ outer (((inner (Sum.inl world)).run).run state.2.1)).run state.2.2 >>=
        fun step => (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2)) :
          ProbComp _) := rfl

theorem fuseServing_run_inr {S : Type} (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S) (request : Message)
    (state : ω × SigningLog × S) :
    ((fuseServing outer inner before after) (Sum.inr request)).run state =
      (simulateQ outer (((inner (Sum.inr request)).run).run state.2.1)).run
          (before request state.2.2) >>= fun step =>
        (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _) := rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The fused handler's run factorises through blocks drawn once**, with an arbitrary
continuation on each side. Every case is one application of
`NoticingTape.evalDist_noticingSplitTapeRun_cont` to the nested run, with this induction's
hypothesis at the tail supplying that lemma's hypothesis. -/
theorem evalDist_fusedSplitTapeRun_cont (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ)
    {α γ : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (handlerAfter : α × (ω × SigningLog × StateOf σ) → ProbComp γ)
    (tapeAfter :
      α × (ω × SigningLog × SplitTapeState σ) → ProbComp γ)
    (hafter : ∀ (leftLength rightLength : Nat)
        (z : α × (ω × SigningLog × StateOf σ)),
      𝒟[handlerAfter z] =
        𝒟[padding leftLength >>= fun leftTape => padding rightLength >>= fun rightTape =>
            tapeAfter (z.1, (z.2.1, z.2.2.1,
              (z.2.2.2.1, (leftTape, rightTape), z.2.2.2.2)))]) :
    ∀ (leftLength rightLength : Nat) (accumulated : ω) (log : SigningLog)
      (cache : σ) (leftRecord rightRecord : Record),
      𝒟[(simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
            (fun request => onCarrier (before request)) (onCarrier after)) phase).run
            (accumulated, log, (cache, leftRecord, rightRecord)) >>= handlerAfter] =
        𝒟[padding leftLength >>= fun leftTape =>
            padding rightLength >>= fun rightTape =>
              (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
                  (fun request => onCarrierTape (before request)) (onCarrierTape after))
                phase).run
                  (accumulated, log, (cache, (leftTape, rightTape), (leftRecord, rightRecord)))
                >>= tapeAfter] := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro leftLength rightLength accumulated log cache leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hafter leftLength rightLength (value, (accumulated, log, (cache, leftRecord,
      rightRecord)))
  | query_bind queried next ih =>
    intro leftLength rightLength accumulated log cache leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with world | request
    · simp only [fuseServing_run_inl, bind_assoc, pure_bind]
      refine Eq.trans (evalDist_noticingSplitTapeRun_cont leftKeep rightKeep
        (((inner (Sum.inl world)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
            (fun r => onCarrier (before r)) (onCarrier after)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, z.2) >>= handlerAfter)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape after)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, z.2) >>= tapeAfter)
        (fun lL rL z => ih z.1.1.1 lL rL (accumulated * z.1.1.2) z.1.2 z.2.1 z.2.2.1 z.2.2.2)
        leftLength rightLength cache leftRecord rightRecord) ?_
      rfl
    · simp only [fuseServing_run_inr, bind_assoc, pure_bind]
      refine Eq.trans (evalDist_noticingSplitTapeRun_cont leftKeep rightKeep
        (((inner (Sum.inr request)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner
            (fun r => onCarrier (before r)) (onCarrier after)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, onCarrier after z.2) >>= handlerAfter)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape after)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, onCarrierTape after z.2) >>= tapeAfter)
        (fun lL rL z => ih z.1.1.1 lL rL (accumulated * z.1.1.2) z.1.2 (after z.2.1) z.2.2.1
          z.2.2.2)
        leftLength rightLength (before request cache) leftRecord rightRecord) ?_
      rfl

/-! ## The three stages, factorised through one pair of blocks

The shape `BracketedRun.IsBracketedRecorderRun` describes: key generation under the handler, the
adversary's phase fused and bracketed, verification under the handler again. Three runs, and the
blocks are drawn **once, before the first of them**.

The proof is three applications and no induction. Each stage's continuation is the next stage,
and each stage's factorisation supplies the hypothesis the previous one asked for; the last
stage's continuation ignores what is left of the blocks, which is the dropped-block case the
one-run statement was. That the three fit together with nothing between them is the whole return
on stating both factorisations with a continuation.
-/

/-- The projection the bracketed shape reads its state through, at a general view. -/
def forgetView (state : StateOf σ) : SplitPrefix.SplitState :=
  (CacheView.cacheOf state.1, state.2)

/-- The same projection from the tape recorder's state: the blocks go with the carrier. -/
def forgetViewTape (state : SplitTapeState σ) : SplitPrefix.SplitState :=
  (CacheView.cacheOf state.1, state.2.2)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A three-stage bracketed run factorises through one pair of blocks drawn at the top.** -/
theorem evalDist_threeStage (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → SigningLog → γ → δ)
    (leftLength rightLength : Nat) (cache : σ) (leftRecord rightRecord : Record) :
    𝒟[(simulateQ (noticingRecorderOf leftKeep rightKeep) first).run
          (cache, leftRecord, rightRecord) >>= fun keys =>
        (simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) (inner keys.1)
            (fun request => onCarrier (before request)) (onCarrier after))
          (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
          (simulateQ (noticingRecorderOf leftKeep rightKeep)
              (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
            (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetView final.2) :
              ProbComp (δ × SplitPrefix.SplitState))] =
      𝒟[padding leftLength >>= fun leftTape =>
          padding rightLength >>= fun rightTape =>
            (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) first).run
                (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= fun keys =>
              (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep)
                  (inner keys.1) (fun request => onCarrierTape (before request))
                  (onCarrierTape after)) (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
                (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                    (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
                  (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
                    forgetViewTape final.2) :
                    ProbComp (δ × SplitPrefix.SplitState))] := by
  classical
  refine evalDist_noticingSplitTapeRun_cont leftKeep rightKeep first
    (fun keys => (simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) (inner keys.1)
        (fun request => onCarrier (before request)) (onCarrier after))
        (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
          (simulateQ (noticingRecorderOf leftKeep rightKeep) (last keys.1 middle.1)).run
            middle.2.2.2 >>= fun final =>
              (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetView final.2) :
                ProbComp (δ × SplitPrefix.SplitState)))
    (fun keys => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep)
        (inner keys.1) (fun request => onCarrierTape (before request)) (onCarrierTape after))
        (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) (last keys.1 middle.1)).run
            middle.2.2.2 >>= fun final =>
              (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
                forgetViewTape final.2) : ProbComp (δ × SplitPrefix.SplitState)))
    ?_ leftLength rightLength cache leftRecord rightRecord
  intro firstLeft firstRight keys
  refine evalDist_fusedSplitTapeRun_cont leftKeep rightKeep (inner keys.1) before after
    (phase keys.1)
    (fun middle => (simulateQ (noticingRecorderOf leftKeep rightKeep)
        (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetView final.2) :
            ProbComp (δ × SplitPrefix.SplitState)))
    (fun middle => (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
        (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetViewTape final.2) :
            ProbComp (δ × SplitPrefix.SplitState)))
    ?_ firstLeft firstRight 1 [] keys.2.1 keys.2.2.1 keys.2.2.2
  intro middleLeft middleRight middle
  refine evalDist_noticingSplitTapeRun_cont leftKeep rightKeep (last keys.1 middle.1)
    (fun final => (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
      forgetView final.2) : ProbComp (δ × SplitPrefix.SplitState)))
    (fun final => (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
      forgetViewTape final.2) : ProbComp (δ × SplitPrefix.SplitState)))
    ?_ middleLeft middleRight middle.2.2.2.1 middle.2.2.2.2.1 middle.2.2.2.2.2
  intro lastLeft lastRight final
  have hconst : ∀ leftTape rightTape : List HashOutput,
      (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
          forgetViewTape (final.2.1, (leftTape, rightTape), final.2.2)) :
        ProbComp (δ × SplitPrefix.SplitState)) =
      pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetView final.2) :=
    fun _ _ => rfl
  simp only [hconst]
  rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding lastLeft)
      (padding_neverFails lastLeft),
    OracleComp.DeferredSampling.evalDist_bind_const_neverFails (padding lastRight)
      (padding_neverFails lastRight)]

/-! ## The two facts the charge composes by itself

Never failing and never shortening the target recording both compose across a bind without a
continuation parameter, so they are ordinary inductions. The brackets are invisible to the
second for the reason they are invisible to everything else here: `onCarrierTape` changes the
carrier and nothing else, so the recordings it leaves are the ones it was given.
-/

open scoped Classical in
/-- **The fused tape-reading run never fails.** -/
theorem fusedSplitTapeRun_neverFails (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ state : ω × SigningLog × SplitTapeState σ,
      Pr[⊥ | (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
        (fun request => onCarrierTape (before request)) (onCarrierTape afterMap)) phase).run
          state] = 0 := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value => intro state; simp
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨?_, fun step _ => ih step.1 step.2⟩
    rcases queried with world | request
    · rw [fuseServing_run_inl]
      exact probFailure_bind_eq_zero_iff _ _ |>.mpr
        ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep _ _, fun _ _ => by simp⟩
    · rw [fuseServing_run_inr]
      exact probFailure_bind_eq_zero_iff _ _ |>.mpr
        ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep _ _, fun _ _ => by simp⟩

open scoped Classical in
/-- **The target recording only grows under the fused run.** -/
theorem fusedRightOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : ω × SigningLog × SplitTapeState σ)
      (result : α × (ω × SigningLog × SplitTapeState σ)),
      result ∈ support ((simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep)
        inner (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
          phase).run state) ->
      rightOf state.2.2 <+: rightOf result.2.2.2 := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    intro state result hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine List.IsPrefix.trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with world | request
    · rw [fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact noticingRightOf_prefix leftKeep rightKeep _ _ z hz
    · rw [fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact noticingRightOf_prefix leftKeep rightKeep _
        (onCarrierTape (before request) state.2.2) z hz

/-! ## The selection's causality at the fused handler

The third member of the family, and the same shape as the first two: every case is one nested
run followed by the rest of the phase, so every case is one application of
`NoticingTape.probEvent_length_set_cont` with this induction's own hypothesis at the tail.

The brackets are again invisible. `setRightTape` and `onCarrierTape` touch different components
of the state, so the two commute definitionally and the bracketed case needs nothing said about
it.
-/

/-- Overwrite one cell of the target block, leaving everything else alone. -/
def setRightTape (cell : Nat) (value : HashOutput) (state : SplitTapeState σ) :
    SplitTapeState σ :=
  (state.1, (state.2.1.1, state.2.1.2.set cell value), state.2.2)

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **Overwriting an unread cell does not move the selection, at the fused handler.** -/
theorem probEvent_length_set_fused (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    {α γ : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (cont : α × (ω × SigningLog × SplitTapeState σ) → ProbComp γ)
    (finalRight : γ → Record)
    (hgrow : ∀ (z : α × (ω × SigningLog × SplitTapeState σ))
        (w : γ), w ∈ support (cont z) ->
      (rightOf z.2.2.2).length ≤ (finalRight w).length)
    (hfail : ∀ z, Pr[⊥ | cont z] = 0)
    (hcont : ∀ (index : Nat) (newValue : HashOutput)
        (z : α × (ω × SigningLog × SplitTapeState σ)),
      Pr[fun w => (rightOf z.2.2.2).length + index < (finalRight w).length | cont z] =
        Pr[fun w => (rightOf z.2.2.2).length + index < (finalRight w).length |
          cont (z.1, (z.2.1, z.2.2.1, setRightTape index newValue z.2.2.2))]) :
    ∀ (index : Nat) (newValue : HashOutput) (accumulated : ω) (log : SigningLog)
      (cache : σ) (leftTape rightTape : List HashOutput) (leftRecord rightRecord : Record),
      Pr[fun w => rightRecord.length + index < (finalRight w).length |
          (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
            phase).run (accumulated, log, (cache, (leftTape, rightTape),
              (leftRecord, rightRecord))) >>= cont] =
        Pr[fun w => rightRecord.length + index < (finalRight w).length |
          (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
            phase).run (accumulated, log, (cache, (leftTape, rightTape.set index newValue),
              (leftRecord, rightRecord))) >>= cont] := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro index newValue accumulated log cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hcont index newValue
      (value, (accumulated, log, (cache, (leftTape, rightTape), (leftRecord, rightRecord))))
  | query_bind queried next ih =>
    intro index newValue accumulated log cache leftTape rightTape leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with world | request
    · simp only [fuseServing_run_inl, bind_assoc, pure_bind]
      exact NoticingTape.probEvent_length_set_cont leftKeep rightKeep
        (((inner (Sum.inl world)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape afterMap)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, z.2) >>= cont)
        finalRight
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨r, hr, hw2⟩ := hw
          exact le_trans (fusedRightOf_prefix leftKeep rightKeep inner before afterMap _
            (accumulated * z.1.1.2, z.1.2, z.2) r hr).length_le (hgrow r w hw2))
        (fun z => probFailure_bind_eq_zero_iff _ _ |>.mpr
          ⟨fusedSplitTapeRun_neverFails leftKeep rightKeep inner before afterMap _ _,
            fun r _ => hfail r⟩)
        (fun idx v z => ih z.1.1.1 idx v (accumulated * z.1.1.2) z.1.2 z.2.1 z.2.2.1.1
          z.2.2.1.2 z.2.2.2.1 z.2.2.2.2)
        index newValue cache leftTape rightTape leftRecord rightRecord
    · simp only [fuseServing_run_inr, bind_assoc, pure_bind]
      exact NoticingTape.probEvent_length_set_cont leftKeep rightKeep
        (((inner (Sum.inr request)).run).run log)
        (fun z => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) inner
            (fun r => onCarrierTape (before r)) (onCarrierTape afterMap)) (next z.1.1.1)).run
            (accumulated * z.1.1.2, z.1.2, onCarrierTape afterMap z.2) >>= cont)
        finalRight
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨r, hr, hw2⟩ := hw
          exact le_trans (fusedRightOf_prefix leftKeep rightKeep inner before afterMap _
            (accumulated * z.1.1.2, z.1.2, onCarrierTape afterMap z.2) r hr).length_le
            (hgrow r w hw2))
        (fun z => probFailure_bind_eq_zero_iff _ _ |>.mpr
          ⟨fusedSplitTapeRun_neverFails leftKeep rightKeep inner before afterMap _ _,
            fun r _ => hfail r⟩)
        (fun idx v z => ih z.1.1.1 idx v (accumulated * z.1.1.2) z.1.2
          (afterMap z.2.1) z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2)
        index newValue (before request cache) leftTape rightTape leftRecord rightRecord

/-! ## The three stages, and the selection's causality across all three

The last application-level step of the family. Three nested applications again, in the same
order and for the same reason: each layer's hypothesis is the next layer's conclusion. The
innermost one is `rfl`, because the final `pure` reads its state through `forgetViewTape` and
that drops the blocks — overwriting a cell of a block the answer no longer mentions cannot
change the answer.
-/

/-- The tape-reading three-stage run, named so the charge can be stated at it. -/
noncomputable def threeStageTapeRun (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → SigningLog → γ → δ)
    (cache : σ) (leftRecord rightRecord : Record)
    (leftTape rightTape : List HashOutput) :
    ProbComp (δ × SplitPrefix.SplitState) :=
  (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) first).run
      (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= fun keys =>
    (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep) (inner keys.1)
        (fun request => onCarrierTape (before request)) (onCarrierTape afterMap))
      (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
      (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
          (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
        (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetViewTape final.2) :
          ProbComp (δ × SplitPrefix.SplitState))

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **Overwriting an unread cell does not move the selection, across all three stages.** -/
theorem probEvent_length_set_threeStage (leftKeep rightKeep : Bytes → σ → Prop)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (value : β → α → ω → SigningLog → γ → δ)
    (index : Nat) (newValue : HashOutput) (cache : σ)
    (leftRecord rightRecord : Record) (leftTape rightTape : List HashOutput) :
    Pr[fun w : δ × SplitPrefix.SplitState =>
        rightRecord.length + index < w.2.2.2.length |
        threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value cache
          leftRecord rightRecord leftTape rightTape] =
      Pr[fun w : δ × SplitPrefix.SplitState =>
        rightRecord.length + index < w.2.2.2.length |
        threeStageTapeRun leftKeep rightKeep inner before afterMap first phase last value cache
          leftRecord rightRecord leftTape (rightTape.set index newValue)] := by
  classical
  rw [threeStageTapeRun, threeStageTapeRun]
  refine NoticingTape.probEvent_length_set_cont leftKeep rightKeep first
    (fun keys => (simulateQ (fuseServing (noticingSplitTapeRecorder leftKeep rightKeep)
          (inner keys.1) (fun request => onCarrierTape (before request))
          (onCarrierTape afterMap)) (phase keys.1)).run (1, [], keys.2) >>= fun middle =>
        (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
            (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1,
            forgetViewTape final.2) : ProbComp (δ × SplitPrefix.SplitState)))
    (fun w => w.2.2.2) ?_ ?_ ?_ index newValue cache leftTape rightTape leftRecord rightRecord
  · intro z w hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨middle, hmiddle, hrest⟩ := hw
    rw [mem_support_bind_iff] at hrest
    obtain ⟨final, hfinal, hpure⟩ := hrest
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    refine le_trans (fusedRightOf_prefix leftKeep rightKeep (inner z.1) before afterMap _
      (1, [], z.2) middle hmiddle).length_le ?_
    exact (noticingRightOf_prefix leftKeep rightKeep _ middle.2.2.2 final hfinal).length_le
  · intro z
    refine probFailure_bind_eq_zero_iff _ _ |>.mpr
      ⟨fusedSplitTapeRun_neverFails leftKeep rightKeep (inner z.1) before afterMap _ _,
        fun middle _ => ?_⟩
    exact probFailure_bind_eq_zero_iff _ _ |>.mpr
      ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep _ _, fun _ _ => by simp⟩
  · intro idx v z
    refine probEvent_length_set_fused leftKeep rightKeep (inner z.1) before afterMap
      (phase z.1)
      (fun middle => (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
            (last z.1 middle.1)).run middle.2.2.2 >>= fun final =>
          (pure (value z.1 middle.1 middle.2.1 middle.2.2.1 final.1, forgetViewTape final.2) :
            ProbComp (δ × SplitPrefix.SplitState)))
      (fun w => w.2.2.2) ?_ ?_ ?_ idx v 1 [] z.2.1 z.2.2.1.1 z.2.2.1.2 z.2.2.2.1 z.2.2.2.2
    · intro y w hw
      rw [mem_support_bind_iff] at hw
      obtain ⟨final, hfinal, hpure⟩ := hw
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact (noticingRightOf_prefix leftKeep rightKeep _ y.2.2.2 final hfinal).length_le
    · intro y
      exact probFailure_bind_eq_zero_iff _ _ |>.mpr
        ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep _ _, fun _ _ => by simp⟩
    · intro idx2 v2 y
      refine NoticingTape.probEvent_length_set_cont leftKeep rightKeep (last z.1 y.1)
        (fun final => (pure (value z.1 y.1 y.2.1 y.2.2.1 final.1, forgetViewTape final.2) :
          ProbComp (δ × SplitPrefix.SplitState)))
        (fun w => w.2.2.2) ?_ ?_ ?_ idx2 v2 y.2.2.2.1 y.2.2.2.2.1.1 y.2.2.2.2.1.2
        y.2.2.2.2.2.1 y.2.2.2.2.2.2
      · intro t w hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact le_rfl
      · intro t
        simp
      · intro idx3 v3 t
        rfl

end SlhDsaSecurity.FusedTape

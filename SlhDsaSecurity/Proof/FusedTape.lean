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

end SlhDsaSecurity.FusedTape

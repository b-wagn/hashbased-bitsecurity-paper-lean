import SlhDsaSecurity.Proof.WriterState
import SlhDsaSecurity.Proof.KeygenUniform

/-!
# The signer, inside the stack the charge simulates

`PROGRESS.md` has called this the deepest of the obstructions: the charge simulates one handler
over `OracleWorld`, and the signing oracle sits *outside* that simulation, so by the time the
charge sees a query it cannot tell whose it is. Anything the signing oracle would like to tell
the charge — that it is serving, and which request — has nowhere to go.

Nothing about the game has to change for it to go somewhere. The game's phase is

    simulateQ outer (((simulateQ inner computation).run).run log)

with `inner` the adversary-and-signing handler into a writer over the log over `OracleComp
OracleWorld`, and `outer` whatever handler the charge simulates. `fuse` is the same two steps
taken as one: a single handler on `OracleWorld + SigningSpec` into `StateT (ω × SigningLog × S)
ProbComp`, whose every step runs `inner`'s step and then `outer` on what it emitted. `run_fuse`
is that it is the same computation — not the same law, the same computation.

What that buys is the whole point. In the fused handler a signing request is **one step**, and
that step has `outer`'s state in hand on both sides of the signer's sub-run. A variant that sets
a flag before the sub-run and clears it after is then an ordinary handler, writing to its own
state, with no change to what the game computes; the sub-run's queries are `outer`'s to see,
tagged. Before the fusion there was no such place to stand.

The writer's monoid is a parameter, so this serves `Security.CountedRun` and
`SplitRecorder.SplitRun` alike, and `WriterState.run_toStateful` is its one-level-down
counterpart: that moves a writer into a state at a fixed base monad, this moves a whole
two-layer run under an outer simulation.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.PhaseFusion

open Security

variable {ω : Type} [Monoid ω] {S : Type}

/-- The phase's two handlers as one: `inner`'s step, then `outer` on what it emitted, with the
writer and the log carried in the state. -/
noncomputable def fuse (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld)))) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (ω × SigningLog × S) ProbComp) :=
  fun queried state => do
    let step ← (simulateQ outer (((inner queried).run).run state.2.1)).run state.2.2
    pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2))

theorem fuse_run (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (queried : (OracleWorld + SigningSpec).Domain) (state : ω × SigningLog × S) :
    ((fuse outer inner) queried).run state =
      (simulateQ outer (((inner queried).run).run state.2.1)).run state.2.2 >>= fun step =>
        pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2)) := rfl

set_option maxHeartbeats 1000000 in
/-- **The fusion is an equality of computations.** Running the phase's two handlers one after the
other is running the fused one, with the writer's accumulation multiplied onto what the state
came in with. -/
theorem run_fuse {α : Type} (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (state : S),
      (simulateQ (fuse outer inner) computation).run (accumulated, log, state) =
        (fun step : ((α × ω) × SigningLog) × S =>
          (step.1.1.1, (accumulated * step.1.1.2, step.1.2, step.2))) <$>
          (simulateQ outer (((simulateQ inner computation).run).run log)).run state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log state
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure, StateT.run_pure, map_pure,
      mul_one]
  | query_bind queried next ih =>
    intro accumulated log state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, fuse_run, bind_assoc]
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, StateT.run_bind,
      simulateQ_bind, StateT.run_bind, map_bind]
    refine bind_congr fun step => ?_
    rw [pure_bind, ih step.1.1.1 (accumulated * step.1.1.2) step.1.2 step.2]
    simp only [StateT.run_map, simulateQ_map, Functor.map_map, Function.comp_def, mul_assoc]

/-! ## What it is for

The fused handler takes a signing request in one step, with the outer handler's state in hand
before and after the signer's sub-run. `serving` is that step wrapped: set something in the
state, run, clear it. It is stated against an arbitrary pair of state maps because what gets set
is the carrier's business and not the fusion's — `ServingCarrier.setFraming` and `clearFraming`
are the intended pair, and the fusion neither knows nor needs to. -/

/-- The fused handler with the signing step bracketed by two state maps. -/
noncomputable def fuseServing (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (ω × SigningLog × S) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl world => ((fuse outer inner) (Sum.inl world)).run state
    | Sum.inr request => do
        let step ← (simulateQ outer (((inner (Sum.inr request)).run).run state.2.1)).run
          (before request state.2.2)
        pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, after step.2))

/-- **The bracket is the only difference.** With both maps the identity, the serving handler is
the fused one — so nothing about the presentation depends on what is set, and a proof that the
game is unchanged by the bookkeeping is a proof about `before` and `after` alone. -/
theorem fuseServing_id (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld)))) :
    fuseServing outer inner (fun _ state => state) (fun state => state) = fuse outer inner := by
  funext queried state
  rcases queried with world | request <;> rfl

end SlhDsaSecurity.PhaseFusion

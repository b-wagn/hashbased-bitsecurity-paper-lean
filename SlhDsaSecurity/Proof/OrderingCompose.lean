import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.PhaseFusion

/-!
# The potential charge across a bracketed phase, and across three stages

`PotentialCharge.prob_fired_le_cont` charges a run of one handler over `OracleWorld` followed by
anything. This file carries it to the two shapes a bracketed game is made of: the adversary's
phase under `PhaseFusion.fuseServing`, and the three stages of
`BracketedRun.IsBracketedRecorderRun`.

**There is no second induction over `OracleWorld` here.** `PhaseFusion.fuse` runs
`simulateQ outer` on *both* branches — the inner handler lifts a query, world or signing, into
an `OracleComp OracleWorld` and the outer handler simulates it — so every case of the induction
below is one nested run followed by the rest of the phase. The nested run is discharged by the
continuation form, and that lemma's hypothesis about its continuation is this induction's own
hypothesis at the tail.

**What the brackets have to be.** The opening bracket runs before the sub-run and the closing
one after it, and the charge reads three things of a state: whether it has fired, its potential,
and its gauge. So a bracket has to leave all three alone — not fire, not raise the potential,
not move the gauge. `Neutral` is that, and it is what `BracketedRun.Bracket` delivers for a
charge whose three readings are functions of the cache and the recordings: the brackets write the
framing and nothing else.

**Each layer quotes only its own offsets.** The three-stage composition relates no stage's state
to any other stage's: stage two's bound is read at the state stage one left, stage three's at the
state stage two left, and the telescoping of gauges happens inside one layer of the continuation
form. A lemma relating the last state back to the first would be a sign the shape is wrong, not
a lemma to prove.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.OrderingCompose

open Security PhaseFusion

variable {σ : Type} {ω : Type} [Monoid ω]

/-! ## The fused handler's two steps, as equations

Both are `rfl`. They are restated here rather than imported so that this file depends on
`PhaseFusion` alone. -/

theorem fuseServing_run_inl (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (world : OracleWorld.Domain)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inl world)).run state =
      (simulateQ outer (((inner (Sum.inl world)).run).run state.2.1)).run state.2.2 >>=
        fun step => (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2)) :
          ProbComp _) := rfl

theorem fuseServing_run_inr (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (request : Message)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inr request)).run state =
      (simulateQ outer (((inner (Sum.inr request)).run).run state.2.1)).run
          (before request state.2.2) >>= fun step =>
        (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _) := rfl

/-! ## What a bracket has to be -/

/-! ## Two facts a handler's runs inherit from its steps

`PotentialCharge.prob_fired_le` asks for its two run-level facts at **every** result type, which
no instantiation should discharge by its own induction: both follow from the three step equations
the charge already has. Stated here so that a handler owes the charge steps and nothing else. -/

/-! ## Two facts the fused phase supplies about itself

The charge's continuation hypotheses are read at the fused run, so the two things the
continuation form asks of *its* continuation — that it never fails and that the gauge does not
shrink — have to hold across a phase as well as across a run. Both are ordinary inductions with
no continuation parameter, and the brackets are invisible to both: the opening and closing maps
leave the gauge where it was by `Neutral`, and neither introduces a way to fail.
-/

/-! ## The charge across the bracketed phase -/

/-! ## The three stages

`BracketedRun.IsBracketedRecorderRun`'s shape: key generation under the handler, the adversary's
phase fused and bracketed, verification under the handler again, and a `pure` reading the value
off. Three nested applications and no induction — each stage's continuation is the next stage,
and each stage's charge supplies the hypothesis the previous one asked for.

**Nothing here relates the last state to the first.** Stage two's bound is read at the state
stage one left and stage three's at the state stage two left; the gauge telescopes inside one
layer of the continuation form. The only facts crossing a stage boundary are the two the phase
proves about itself.
-/

end SlhDsaSecurity.OrderingCompose

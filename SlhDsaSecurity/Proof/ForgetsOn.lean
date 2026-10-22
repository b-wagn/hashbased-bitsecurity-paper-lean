import SlhDsaSecurity.Proof.ServingForget
import SlhDsaSecurity.Proof.WalkTable
import SlhDsaSecurity.Proof.HandlerComparison

/-!
# Forgetting along a map, where the two handlers only agree on some states

`ServingForget.ForgetsAlong` says two handlers' runs agree through a projection, **at every
state**, as an equality of computations. That is the right statement when the two handlers agree
unconditionally, and it has consumers whose proofs rest on it being unconditional. This file does
not touch it.

What the seed hop needs is the same thing on a **subset** of states: the real carrier handler and
the one that keeps the signer's randomisers in a separate table agree at every query *while a
request is in flight*, and not otherwise — the whole content of the hop is that they differ once
the framing drops. So the condition cannot be dropped, and the unconditional form cannot be
weakened to admit it without breaking its existing callers.

**Two things change when the agreement is conditional, and only one of them is a choice.**

The condition has to be *maintained* by the steps, which is a hypothesis here and is discharged
at the carrier by `ServedAgreement.Files.runFraming` — a request in flight stays in flight for a
whole sub-run, which is what makes "the signer's queries" a set of steps rather than a guess.

And the conclusion has to be an equality of **distributions** rather than of computations. That
is forced, not chosen: the induction's hypothesis is only available at states the previous step
can actually reach, so the two continuations agree on the run's support and nowhere else, and
`WalkTable.evalDist_bind_congr_support` is the only congruence that asks for no more. The
unconditional form can use `bind_congr` precisely because it has nothing to condition on.

That is no loss for the hop: `HandlerComparison.prob_bad_eq` asks for its steps to agree as
distributions.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForgetsOn

open Security

variable {S S' : Type}

/-- **Forgetting along a map, on the states a predicate admits.** The distribution-level,
conditional sibling of `ServingForget.ForgetsAlong`. -/
def ForgetsLawOn (P : S → Prop) (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp)) : Prop :=
  ∀ {β : Type} (computation : OracleComp OracleWorld β) (state : S), P state →
    𝒟[(fun z : β × S => (z.1, π z.2)) <$> (simulateQ outer computation).run state] =
      𝒟[(simulateQ outer' computation).run (π state)]

set_option maxHeartbeats 1000000 in
/-- **A conditional agreement at every step is a conditional agreement at every run.** The two
hypotheses are the ones the condition forces: the steps agree where the predicate holds, and the
predicate survives a step taken where it holds. -/
theorem forgetsLawOn_of_step (P : S → Prop) (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hstep : ∀ (queried : OracleWorld.Domain) (state : S), P state →
      𝒟[(fun z : OracleWorld.Range queried × S => (z.1, π z.2)) <$> ((outer queried).run state)] =
        𝒟[(outer' queried).run (π state)])
    (hpreserve : ∀ (queried : OracleWorld.Domain) (state : S), P state →
      ∀ step ∈ support ((outer queried).run state), P step.2) :
    ForgetsLawOn P π outer outer' := by
  classical
  intro β computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hstate
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state hstate
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, map_bind]
    calc 𝒟[(outer queried).run state >>= fun step =>
            (fun z : β × S => (z.1, π z.2)) <$> (simulateQ outer (next step.1)).run step.2]
        = 𝒟[(outer queried).run state >>= fun step =>
            (simulateQ outer' (next step.1)).run (π step.2)] :=
          WalkTable.evalDist_bind_congr_support _ _ _ fun step hmem =>
            ih step.1 step.2 (hpreserve queried state hstate step hmem)
      _ = 𝒟[((fun z : OracleWorld.Range queried × S => (z.1, π z.2)) <$>
            (outer queried).run state) >>= fun step =>
              (simulateQ outer' (next step.1)).run step.2] := by
          rw [bind_map_left]
      _ = 𝒟[(outer' queried).run (π state) >>= fun step =>
            (simulateQ outer' (next step.1)).run step.2] :=
          HandlerComparison.evalDist_bind_congr (hstep queried state hstate) _

end SlhDsaSecurity.ForgetsOn

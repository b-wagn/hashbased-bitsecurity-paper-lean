import SlhDsaSecurity.Proof.FusedGame

/-!
# What the brackets are invisible to

The carrier tail the ordering term needs runs the game under a handler that **files** and under
a signing oracle that raises and lowers a **framing**. Both are new, and the first question every
consumer asks is what they change. The answer is: the recordings and the carrier, and nothing
else. This file is that answer, stated once and generically, so that the equations such a tail
owes are instances of one lemma rather than three inductions.

**It has to be a projection law, because the brackets are not invisible to the handler.** A
filing test that reads the framing is exactly a test whose answer the brackets change — that is
what they are for. What is invisible is everything a projection keeps. Give a map `π` out of the
outer state that the brackets leave alone and that the handler's own runs commute with, and the
bracketed phase **is** the unbracketed one through `π`.

For the carrier that map is "take the cache": the handler's runs commute with it because the
recorder answers exactly as the shared oracle does, and the brackets leave it alone because they
write only the framing. So the game's forgery, its log, its counts and its cache come out
unchanged, while the recordings — which `π` drops — are free to differ. They must: the left
recording is the thing the brackets exist to change.

**The three statements it serves.** At `π` = "forget the recordings" this is what
`LateProbes.ForgetsTo` asks for; at `π` = "forget the record as well" it is the
`FinalAssembly.forgetFused_map` analogue; at the answer side's own projection it is
`AnswerShape.map_fusedTail`'s. One induction serves all three, and a reader who wants to know
what a bracket costs reads one statement rather than hunting three.

`run_servingAfterSeeds_map` is the `FusedGame.run_afterSeeds_fused` analogue with real brackets:
the whole game, phase bracketed, projecting to the game as it was. Key generation and
verification run under the handler directly and so need the same commuting law; the phase needs
it through the fusion, which is `run_fuseServing_map`.

**What this file does not say.** Nothing here claims a bracketed run is a
`LateProbes.IsRecorderRun`. It is not, and cannot be made one: that predicate demands the tail
be `simulateQ (recorder …) computation` for a `computation : OracleComp OracleWorld _`, and such
a computation can only sample or query — it has no way to carry a frame. The brackets write the
state *between* queries. What is proved here is that this is the only thing they do, which is
what makes the generalisation of that predicate safe rather than hopeful.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingForget

open Security PhaseFusion

variable {ω : Type} [Monoid ω] {S S' : Type}

/-- **A handler forgets along `π`**: running it and projecting is projecting and running. The
only thing a bracketed presentation asks of the handler underneath it. -/
def ForgetsAlong (π : S → S') (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp)) : Prop :=
  ∀ {β : Type} (computation : OracleComp OracleWorld β) (state : S),
    (fun z : β × S => (z.1, π z.2)) <$> (simulateQ outer computation).run state =
      (simulateQ outer' computation).run (π state)

set_option maxHeartbeats 1000000 in
/-- **One step of the bracketed phase is one step of the unbracketed one, through `π`.** The
adversary's step is the fused step unchanged; the signing step brackets, and `π` cannot see
the bracket. -/
theorem run_fuseServing_step_map (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hbefore : ∀ (request : Message) (state : S), π (before request state) = π state)
    (hafter : ∀ state : S, π (after state) = π state)
    (hforget : ForgetsAlong π outer outer')
    (queried : (OracleWorld + SigningSpec).Domain) (accumulated : ω) (log : SigningLog)
    (state : S) :
    (fun step : (OracleWorld + SigningSpec).Range queried × (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuseServing outer inner before after) queried).run (accumulated, log, state) =
      ((fuse outer' inner) queried).run (accumulated, log, π state) := by
  rcases queried with world | request
  · show (fun step : (OracleWorld + SigningSpec).Range (Sum.inl world) × (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((fuse outer inner) (Sum.inl world)).run (accumulated, log, state) = _
    rw [fuse_run, fuse_run, map_eq_bind_pure_comp, bind_assoc,
      ← hforget (((inner (Sum.inl world)).run).run log) state, map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun step => ?_
    simp [Function.comp_def]
  · show (fun step : (OracleWorld + SigningSpec).Range (Sum.inr request) × (ω × SigningLog × S) =>
        (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
      ((simulateQ outer (((inner (Sum.inr request)).run).run log)).run (before request state) >>=
        fun step => (pure (step.1.1.1, (accumulated * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _)) = _
    rw [fuse_run]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, hafter]
    conv_rhs => rw [← hbefore request state,
      ← hforget (((inner (Sum.inr request)).run).run log) (before request state)]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

set_option maxHeartbeats 1000000 in
/-- **And therefore the whole phase.** -/
theorem run_fuseServing_map (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (after : S → S)
    (hbefore : ∀ (request : Message) (state : S), π (before request state) = π state)
    (hafter : ∀ state : S, π (after state) = π state)
    (hforget : ForgetsAlong π outer outer') {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (state : S),
      (fun step : α × (ω × SigningLog × S) =>
          (step.1, (step.2.1, step.2.2.1, π step.2.2.2))) <$>
        (simulateQ (fuseServing outer inner before after) computation).run
          (accumulated, log, state) =
      (simulateQ (fuse outer' inner) computation).run (accumulated, log, π state) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log state
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro accumulated log state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      ← run_fuseServing_step_map π outer outer' inner before after hbefore hafter hforget queried
        accumulated log state,
      bind_map_left]
    refine bind_congr fun step => ?_
    exact ih step.1 step.2.1 step.2.2.1 step.2.2.2

/-- The game with its adversary phase bracketed: `FusedGame.run_afterSeeds_fused`'s right-hand
side with `fuseServing` in place of `fuse`. -/
noncomputable def servingAfterSeeds (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (before : Message → S → S) (after : S → S) (adversary : Adversary)
    (sds : Digest × Digest × Digest) (state : S) : ProbComp (Outcome × S) :=
  (simulateQ outer (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run state >>= fun keys =>
    (simulateQ (fuseServing outer (FusedGame.gameInner keys.1.1) before after)
      (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun phase =>
      (simulateQ outer (countQueries
        (fun input => Counts.single .verification (hashCost input))
        (Scheme.verify keys.1.2 phase.1.message phase.1.signature))).run phase.2.2.2 >>=
        fun verified =>
          (pure ({
            forgery := phase.1
            signed := phase.2.2.1
            verified := verified.1.1
            counts := Multiplicative.toAdd phase.2.1 + verified.1.2 }, verified.2) :
            ProbComp (Outcome × S))

set_option maxHeartbeats 1000000 in
/-- **The bracketed game projects to the game.** The `run_afterSeeds` analogue with real
brackets, and the equation a carrier tail owes the target: the value and everything `π` keeps
are what they were, so no probability, count or support that reads only those moves. -/
theorem run_servingAfterSeeds_map (π : S → S')
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (before : Message → S → S) (after : S → S)
    (hbefore : ∀ (request : Message) (state : S), π (before request state) = π state)
    (hafter : ∀ state : S, π (after state) = π state)
    (hforget : ForgetsAlong π outer outer')
    (adversary : Adversary) (sds : Digest × Digest × Digest) (state : S) :
    (fun z : Outcome × S => (z.1, π z.2)) <$>
        servingAfterSeeds outer before after adversary sds state =
      (simulateQ outer' (WarmedGame.afterSeeds adversary sds)).run (π state) := by
  rw [FusedGame.run_afterSeeds_fused outer' adversary sds (π state), servingAfterSeeds, map_bind,
    ← hforget (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2) state, bind_map_left]
  refine bind_congr fun keys => ?_
  rw [map_bind, ← run_fuseServing_map π outer outer' (FusedGame.gameInner keys.1.1) before after
    hbefore hafter hforget (adversary.main keys.1.2) 1 [] keys.2, bind_map_left]
  refine bind_congr fun phase => ?_
  rw [map_bind, ← hforget (countQueries
      (fun input => Counts.single .verification (hashCost input))
      (Scheme.verify keys.1.2 phase.1.message phase.1.signature)) phase.2.2.2, bind_map_left]
  refine bind_congr fun verified => ?_
  simp [Function.comp_def]

end SlhDsaSecurity.ServingForget

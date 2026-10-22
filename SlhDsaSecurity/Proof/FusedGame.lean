import SlhDsaSecurity.Proof.PhaseFusion
import SlhDsaSecurity.Proof.WarmedGame

/-!
# The game's three phases, split as an equality, with the middle one fused

`PhaseFusion.run_phase_fused` says what the adversary's phase is when its two handlers are taken
as one. To use it on the game, the game has to be in a shape where that phase is a sub-run one
can rewrite — which means `WarmedGame.afterSeeds` split at its three sequencing points.

**The split is an equality of computations, not of laws, and that is what makes it usable.**
`WarmedSplit` factors the same three points but at the level of *supports*, which is enough to
attribute an entry and not enough to rewrite a sub-run. Here nothing is lost: `afterSeeds` is a
`do` block, `simulateQ` distributes over its binds, and `StateT.run` distributes over those — so
the split is the definition read out, and it composes with anything.

`run_afterSeeds_fused` is the payoff: the game, with its adversary phase a single `simulateQ` of
a handler that has the outer state in hand at every signing request. That is where
`ServingPhase`'s brackets go.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.FusedGame

open Security

variable {S : Type}

/-- The inner handler the game's adversary phase runs under. -/
noncomputable def gameInner (sk : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Counts) (StateT SigningLog (OracleComp OracleWorld))) :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
      (fun input => Counts.single .hash (hashCost input)) + signingOracle sk

set_option maxHeartbeats 1000000 in
/-- **The game splits at its three sequencing points**, as an equality of computations. -/
theorem run_afterSeeds_split (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (adversary : Adversary) (sds : Digest × Digest × Digest) (state : S) :
    (simulateQ outer (WarmedGame.afterSeeds adversary sds)).run state =
      (simulateQ outer (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run state >>=
        fun keys =>
          (simulateQ outer
            (((simulateQ (gameInner keys.1.1) (adversary.main keys.1.2)).run).run [])).run
              keys.2 >>= fun phase =>
            (simulateQ outer (countQueries
              (fun input => Counts.single .verification (hashCost input))
              (Scheme.verify keys.1.2 phase.1.1.1.message phase.1.1.1.signature))).run
                phase.2 >>= fun verified =>
              (pure ({
                forgery := phase.1.1.1
                signed := phase.1.2
                verified := verified.1.1
                counts := Multiplicative.toAdd phase.1.1.2 + verified.1.2 }, verified.2) :
                ProbComp (Outcome × S)) := by
  unfold WarmedGame.afterSeeds gameInner
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]

set_option maxHeartbeats 1000000 in
/-- **The game, with its adversary phase fused.** The middle sub-run is now one `simulateQ` of a
handler whose state carries the outer handler's — so a signing request is one step, with that
state in hand on both sides of the signer. -/
theorem run_afterSeeds_fused (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (adversary : Adversary) (sds : Digest × Digest × Digest) (state : S) :
    (simulateQ outer (WarmedGame.afterSeeds adversary sds)).run state =
      (simulateQ outer (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run state >>=
        fun keys =>
          (simulateQ (PhaseFusion.fuse outer (gameInner keys.1.1))
            (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun phase =>
            (simulateQ outer (countQueries
              (fun input => Counts.single .verification (hashCost input))
              (Scheme.verify keys.1.2 phase.1.message phase.1.signature))).run
                phase.2.2.2 >>= fun verified =>
              (pure ({
                forgery := phase.1
                signed := phase.2.2.1
                verified := verified.1.1
                counts := Multiplicative.toAdd phase.2.1 + verified.1.2 }, verified.2) :
                ProbComp (Outcome × S)) := by
  rw [run_afterSeeds_split outer adversary sds state]
  refine bind_congr fun keys => ?_
  rw [PhaseFusion.run_phase_fused outer (gameInner keys.1.1) (adversary.main keys.1.2) []
    keys.2, bind_map_left]

end SlhDsaSecurity.FusedGame

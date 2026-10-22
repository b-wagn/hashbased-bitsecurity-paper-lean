import SlhDsaSecurity.Proof.WriterState
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating

/-!
# The adversary's phase as a handler the charge can see through

The experiment nests its simulations: the adversary's own computation is simulated against the
pair of oracles *inside* an `OracleComp OracleWorld`, and that result is then simulated again by
whatever answers the world. For the charge this nesting is the problem, because the inner
handler — the signer among them — ends up part of the computation, where its reads of the cell
table are not frozen when the run is stalled.

Composition undoes the nesting. `QueryImpl.Stateful.link` puts an outer handler and an inner one
together into one handler over the product of their states, and `simulateQ_link_run` says that
running the composite *is* the nesting. The only thing standing between the experiment and that
combinator was the writer, which `WriterState.toStateful` has moved into the state.

The frame machinery next door is not what this wants, and the reason is worth recording. A
`Frame`'s two lenses must be *separated*, so `parSumWith` would give the hash half and the
signing half states that cannot interfere — and they would then have been unable to accumulate
into one `Counts` cell. The experiment's single counter would have become two components whose
product is the real count, changing the accounting shape for nothing. The two halves are
already summed over one target monad in the game, so once the writer has moved they are a
single handler, and `link` composes it with the inner one using a product only where one
genuinely belongs: between the outer handler's state and the inner handler's.

So `phaseHandler` is the experiment's own pair of oracles, read as a stateful handler, and
`run_link_phaseHandler` is the identity: simulating the adversary against the composite from
`((1, []), s)` is the experiment's phase followed by the inner handler. Nothing about the game
changes; the signer simply becomes something a handler does rather than something the
computation does.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.LinkedPhase

open Security WriterState

/-- The hash half of the adversary's phase: the world, lifted and charged per query. -/
noncomputable def adversaryImpl : QueryImpl OracleWorld CountedRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    (fun input => Counts.single .hash (hashCost input))

/-- **The experiment's pair of oracles**, with the counts beside the log in one state. -/
noncomputable def phaseHandler (sk : SecretKey) :
    QueryImpl.Stateful OracleWorld (OracleWorld + SigningSpec)
      (Multiplicative Counts × SigningLog) :=
  toStateful (adversaryImpl + signingOracle sk)

/-- **The restated phase runs the experiment's phase.** From no counts and an empty log it is
the experiment's own run, with the log and the counts it accumulated side by side. -/
theorem run_phaseHandler {α : Type} (sk : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : SigningLog) :
    (simulateQ (phaseHandler sk) computation).run (1, log) =
      (fun p : (α × Multiplicative Counts) × SigningLog => (p.1.1, (p.1.2, p.2))) <$>
        ((simulateQ (adversaryImpl + signingOracle sk) computation).run).run log := by
  rw [phaseHandler, run_toStateful]
  simp only [one_mul]

/-- **The nesting is a composition.** Simulating the adversary against the composite handler is
the experiment's phase, simulated in turn by the inner handler — which is where the charge
needs the signer to be. -/
theorem run_link_phaseHandler {α σ : Type} (sk : SecretKey)
    (inner : QueryImpl OracleWorld (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (log : SigningLog) (state : σ) :
    (simulateQ ((phaseHandler sk).link inner) computation).run ((1, log), state) =
      (fun p : (α × (Multiplicative Counts × SigningLog)) × σ =>
          (p.1.1, (p.1.2, p.2))) <$>
        (simulateQ inner ((simulateQ (phaseHandler sk) computation).run (1, log))).run state :=
  QueryImpl.Stateful.simulateQ_link_run (phaseHandler sk) inner computation (1, log) state

end SlhDsaSecurity.LinkedPhase

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

/-! ## The charge, moved into the computation

A handler charges every query that reaches it. That is harmless while it answers the adversary
alone, and wrong as soon as the phases are put under one handler: the verifier's queries, which
the experiment counts as verification work, would be charged as the adversary's hash work on top
of it, and `Counts.work` adds the two.

So the charge moves first. The experiment's pair of oracles *is* an uncharged pair with a cost
told in front of it — a hash call for the adversary's own queries, one signing request for each
request it makes — and `WriterState.run_simulateQ_withAddCost` then puts that cost inside the
computation, where it counts the adversary's phase and nothing else. What is left answering is
`unchargedPhase`, which tells nothing and keeps only the log, so it is already the stateful
handler the composition wants, with no writer left to move.

**A warning for anything else working over the sum spec.**
`(OracleWorld + SigningSpec).Range (Sum.inr request)` and `SigningSpec.Range request` are equal
only semireducibly, so a lemma phrased at the summand will not rewrite an occurrence sitting at
the sum: `rw` reports the pattern missing and `simp` declines without saying why, and unfolding
past it yields terms that are not type-correct at `instances` transparency. The rule is to
phrase each lemma at the index its goal has — `run_unchargedPhase_inr` is about
`unchargedPhase sk (Sum.inr request)`, not about the signer — and to convert the index once,
inside that lemma's own proof, where it is local. No lifting law is involved; an instance search
that fails here is failing downstream of the mismatch and cannot fix it.

The one thing the equality needs is that the signer's body may be lifted into the writer as a
whole rather than a step at a time. That is not definitional — the experiment writes it step by
step — but at the level of runs both sides compute, so the proof is extensionality and then
arithmetic, not a search for a lifting law. -/

/-- What the adversary's phase charges, query by query. -/
def phaseCost : (OracleWorld + SigningSpec).Domain → Counts
  | .inl input => Counts.single .hash (hashCost input)
  | .inr _ => Counts.single .signing 1

/-- The signer with nothing charged: it answers and records, and tells nothing. -/
noncomputable def unchargedSigner (sk : SecretKey) :
    QueryImpl SigningSpec (StateT SigningLog (OracleComp OracleWorld)) := fun request => do
  let answer ← liftM (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))
  modify (fun signed => signed ++ [⟨request, answer⟩])
  return answer

/-- The experiment's pair of oracles with nothing charged: the world forwarded, and the signer
answering and recording. -/
noncomputable def unchargedPhase (sk : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT SigningLog (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld)) + unchargedSigner sk

/-- The counted run of a lifted state computation, written out. -/
theorem run_liftM_state {α : Type} (x : StateT SigningLog (OracleComp OracleWorld) α)
    (log : SigningLog) :
    ((WriterT.run (liftM x : CountedRun α)).run log) =
      (fun step => ((step.1, (1 : Multiplicative Counts)), step.2)) <$> x.run log := rfl

/-- The counted run of a lifted world computation, written out. -/
theorem run_liftM_world {α : Type} (x : OracleComp OracleWorld α) (log : SigningLog) :
    ((WriterT.run (liftM x : CountedRun α)).run log) =
      (fun value => ((value, (1 : Multiplicative Counts)), log)) <$> x := by
  show (fun step : α × SigningLog => ((step.1, (1 : Multiplicative Counts)), step.2)) <$>
    (x >>= fun value => pure (value, log)) = _
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

/-- A cost told in front of a lifted state computation. -/
theorem run_tell_liftM {α : Type} (cost : Counts)
    (x : StateT SigningLog (OracleComp OracleWorld) α) (log : SigningLog) :
    ((WriterT.run ((do tell (Multiplicative.ofAdd cost); liftM x : CountedRun α))).run log) =
      (fun step => ((step.1, Multiplicative.ofAdd cost), step.2)) <$> x.run log := by
  rw [WriterT.run_bind, WriterT.run_tell, StateT.run_bind, StateT.run_pure, pure_bind,
    StateT.run_map, run_liftM_state]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, mul_one]

/-- The uncharged phase's run at a signing request: it signs, appends, and returns. -/
theorem run_unchargedPhase_inr (sk : SecretKey) (request : Message) (log : SigningLog) :
    ((unchargedPhase sk (Sum.inr request)).run log) =
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes)) >>= fun answer =>
        pure (answer, log ++ [⟨request, answer⟩]) := by
  show ((unchargedSigner sk request).run log) = _
  rw [unchargedSigner]
  simp only [StateT.run_bind, StateT.run_liftM, StateT.run_modify, StateT.run_pure,
    bind_assoc, pure_bind]

/-- The experiment's signer's run: it charges one request, signs, appends, and returns. -/
theorem run_charged_signer (sk : SecretKey) (request : Message) (log : SigningLog) :
    ((WriterT.run (signingOracle sk request)).run log) =
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes)) >>= fun answer =>
        pure ((answer, Multiplicative.ofAdd (Counts.single .signing 1)),
          log ++ [⟨request, answer⟩]) := by
  rw [signingOracle]
  simp only [AddWriterT.addTell, WriterT.run_bind, WriterT.run_tell, WriterT.run_monadLift,
    WriterT.run_pure, StateT.run_bind, StateT.run_pure, StateT.run_modify,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
    mul_one, run_liftM_world]

/-- **The experiment's pair of oracles is the uncharged pair, charged in front.** -/
theorem phase_eq (sk : SecretKey) :
    adversaryImpl + signingOracle sk = (unchargedPhase sk).withAddCost phaseCost := by
  funext queried
  cases queried with
  | inl input => rfl
  | inr request =>
    funext log
    show (WriterT.run (signingOracle sk request)).run log =
      (WriterT.run (((unchargedPhase sk).withAddCost phaseCost) (Sum.inr request))).run log
    rw [QueryImpl.withAddCost, QueryImpl.withCost_apply, run_charged_signer, run_tell_liftM,
      run_unchargedPhase_inr]
    simp [phaseCost]

/-- **The phase with its cost inside the computation.** What answers is `unchargedPhase`, which
tells nothing, so a computation lifted alongside the adversary's is not charged for being
there. -/
theorem run_phase_counted (sk : SecretKey) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (WriterT.run (simulateQ (adversaryImpl + signingOracle sk) computation)) =
      simulateQ (unchargedPhase sk)
        ((simulateQ (addCostOracle phaseCost) computation).run) := by
  rw [phase_eq, WriterState.run_simulateQ_withAddCost]

end SlhDsaSecurity.LinkedPhase

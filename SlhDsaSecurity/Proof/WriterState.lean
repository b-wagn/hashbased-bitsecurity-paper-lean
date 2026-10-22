import SlhDsaSecurity.Statement.Security

/-!
# A writer the handler cannot read is a piece of the state

The adversary's phase of the experiment runs in `Security.CountedRun`, a writer of `Counts`
over a state of signing requests over the game's world. The charge, on the other side, wants a
handler in `StateT σ ProbComp`, because that is the only shape `QueryImpl.Stateful` — and with
it the frame machinery that puts two handlers side by side on one state — admits. The writer is
in the way.

It need not be. A writer accumulates a monoid and the handler **cannot read it back**: that is
not an assumption about `Counts`, it is what `WriterT`'s type says, since the only thing a
`WriterT ω m` computation receives is an `m`-value and the only thing it can do with the
accumulated value is multiply more onto it. So the accumulation can equally well be carried in
the state, and `toStateful` does exactly that: the same handler, with its output multiplied
into a state component instead of told to a writer.

`run_toStateful` is the transport, and it is an equality of computations rather than of laws:
running the restated handler from `(w, s)` is running the original from `s` and multiplying `w`
onto whatever it accumulated. Nothing about the experiment changes — `CountedRun` and
`Security.signingOracle` are the experiment and stay exactly as they are — which is the point
of proving the transport rather than redefining them.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.WriterState

variable {ι : Type} {E : OracleSpec ι} {ω σ : Type} [Monoid ω]
  {M : Type → Type} [Monad M] [LawfulMonad M]

/-- The same handler, carrying what it accumulates in the state instead of in a writer. -/
def toStateful (h : QueryImpl E (WriterT ω (StateT σ M))) :
    QueryImpl E (StateT (ω × σ) M) :=
  fun queried state => do
    let step ← ((h queried).run).run state.2
    pure (step.1.1, (state.1 * step.1.2, step.2))

omit [LawfulMonad M] in
theorem toStateful_run (h : QueryImpl E (WriterT ω (StateT σ M))) (queried : E.Domain)
    (state : ω × σ) :
    ((toStateful h) queried).run state =
      ((h queried).run).run state.2 >>= fun step =>
        pure (step.1.1, (state.1 * step.1.2, step.2)) := rfl

/-- **The transport.** A run of the restated handler is a run of the original with the
accumulated value multiplied onto the one the state came in with. -/
theorem run_toStateful {α : Type} (h : QueryImpl E (WriterT ω (StateT σ M)))
    (computation : OracleComp E α) :
    ∀ (w : ω) (s : σ),
      (simulateQ (toStateful h) computation).run (w, s) =
        (fun p : (α × ω) × σ => (p.1.1, (w * p.1.2, p.2))) <$>
          ((simulateQ h computation).run).run s := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro w s
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure, map_pure, mul_one]
  | query_bind queried next ih =>
    intro w s
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, toStateful_run,
      simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, StateT.run_bind, bind_assoc,
      map_bind]
    refine bind_congr fun step => ?_
    rw [pure_bind, ih step.1.1 (w * step.1.2) step.2, StateT.run_map, Functor.map_map]
    refine congrArg (· <$> ((simulateQ h (next step.1.1)).run).run step.2) ?_
    funext p
    simp only [mul_assoc]

/-! ## The experiment's own signing oracle

The transport applies to it as it stands: `Security.CountedRun` is a writer of `Counts` — a
monoid in its multiplicative guise — over a state of signing requests, so its counts and its log
sit side by side in one state, which is the shape a stateful handler takes. The oracle itself is
untouched; this is the same handler read differently. -/

open Security in
/-- The experiment's signing oracle, with its counts beside its log in one state. -/
noncomputable def statefulSigningOracle (sk : SecretKey) :
    QueryImpl SigningSpec
      (StateT (Multiplicative Counts × SigningLog) (OracleComp OracleWorld)) :=
  toStateful (Security.signingOracle sk)

open Security in
/-- **The restated oracle runs the experiment's.** -/
theorem run_statefulSigningOracle {α : Type} (sk : SecretKey)
    (computation : OracleComp SigningSpec α) (counts : Multiplicative Counts)
    (log : SigningLog) :
    (simulateQ (statefulSigningOracle sk) computation).run (counts, log) =
      (fun p : (α × Multiplicative Counts) × SigningLog =>
        (p.1.1, (counts * p.1.2, p.2))) <$>
          ((simulateQ (Security.signingOracle sk) computation).run).run log :=
  run_toStateful (Security.signingOracle sk) computation counts log

end SlhDsaSecurity.WriterState

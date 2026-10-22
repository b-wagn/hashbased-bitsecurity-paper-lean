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

/-! ## Counting before answering, and counting after

A cost may be charged in two places: by the handler, which tells it as it answers, or by the
computation, which is first rewritten into one that carries its own count and is then answered
by an uncharged handler. The two give the same thing, and the lemma below is that equality.

Which place the charge sits in is not bookkeeping when the handler answers more than one party.
A handler charges every query that reaches it, so a computation that grows — by lifting the
verifier beside the adversary, say — is charged for the newcomer too. A count inside the
computation charges only the part it wraps, and stays put when something else is lifted
alongside. That is why the experiment's counts are moved into the computation before its phases
are put under one handler, and why they come out as the same values afterwards.
-/

theorem run_withAddCost_apply {ι : Type} {spec : OracleSpec ι} {ω : Type} [AddCommMonoid ω]
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ω) (queried : spec.Domain) :
    ((impl.withAddCost costFn) queried).run =
      (fun value => (value, Multiplicative.ofAdd (costFn queried))) <$> impl queried := by
  simp only [QueryImpl.withAddCost, QueryImpl.withCost_apply, WriterT.run_bind,
    WriterT.run_tell, bind_assoc, pure_bind, WriterT.run_monadLift, map_eq_bind_pure_comp,
    Function.comp_def, mul_one]

/-- **The same fact, already applied to a state.**

`run_withAddCost_apply` is stated at the handler, and a proof that has a *state* in hand cannot
rewrite with it: `rw` matches syntax, and `(impl queried >>= pure ∘ f).run state` is not
`(impl queried).run state >>= …` until someone says so. Naming the instance at the level it is
used at is the repair this development has needed more often than any other. -/
theorem run_withAddCost_run {ι : Type} {spec : OracleSpec ι} {ω σ : Type} [AddCommMonoid ω]
    {M : Type → Type} [Monad M] [LawfulMonad M] (impl : QueryImpl spec (StateT σ M))
    (costFn : spec.Domain → ω) (queried : spec.Domain) (state : σ) :
    (((impl.withAddCost costFn) queried).run).run state =
      (impl queried).run state >>= fun p =>
        (pure ((p.1, Multiplicative.ofAdd (costFn queried)), p.2) :
          M ((spec.Range queried × Multiplicative ω) × σ)) := by
  rw [run_withAddCost_apply, StateT.run_map, map_eq_bind_pure_comp]
  rfl

/-- **Counting in the computation is counting in the handler.** -/
theorem run_simulateQ_withAddCost {ι : Type} {spec : OracleSpec ι} {ω : Type} [AddCommMonoid ω]
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ω) {α : Type} (computation : OracleComp spec α) :
    (simulateQ (impl.withAddCost costFn) computation).run =
      simulateQ impl ((simulateQ (addCostOracle costFn) computation).run) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, WriterT.run_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, run_withAddCost_apply,
      simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, addCostOracle,
      run_withAddCost_apply, QueryImpl.ofLift_apply, simulateQ_bind, simulateQ_map,
      simulateQ_spec_query, bind_map_left, bind_map_left]
    refine bind_congr fun value => ?_
    simp only []
    rw [ih value, simulateQ_map, addCostOracle]

/-- **The counted computation, answered.** The shape the experiment uses: the count comes out
as part of the value, and it is the same value the charged handler would have told. -/
theorem simulateQ_run_addCostOracle_map {ι : Type} {spec : OracleSpec ι} {ω : Type}
    [AddCommMonoid ω] {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (costFn : spec.Domain → ω) {α : Type} (computation : OracleComp spec α) :
    simulateQ impl ((fun result => (result.1, Multiplicative.toAdd result.2)) <$>
        (simulateQ (addCostOracle costFn) computation).run) =
      (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
        (simulateQ (impl.withAddCost costFn) computation).run := by
  rw [simulateQ_map, run_simulateQ_withAddCost]

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

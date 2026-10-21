import SlhDsaSecurity.Proof.CacheReplay

/-!
# Two caches that agree off a set touch that set equally often

The input side needs `Pr[the adversary queries a seed-derived input] ≤ q / 2 ^ 128` in the
experiment, where the seed is drawn at key generation. Approximating that experiment by one
that redraws the seed at every step loses `Θ(q / 2 ^ 128)`, which a budget met with equality
cannot absorb — see `Proof/InputCoupling.lean` for why the identical-until-bad hop forces that
redrawing.

The comparison that works is exact. Run the adversary twice: once against the real cache,
which carries the honest entries at seed-derived keys, and once against a blind cache which
does not. The two agree everywhere off those keys, and *the event itself is decided before
they can diverge* — the first seed-derived query both sets the flag and is the first place the
caches differ. So the two runs assign the event the same probability, with no slack.

`prob_touched_eq` below is that statement, proved for an arbitrary set `S` of inputs: two
caches agreeing off `S` give the same probability of touching `S`. Applying it at `S` = the
seed-derived keys leaves `SecretGuessCharge.prob_run_guesses_secret_le` to finish on the blind
side, where the view is seed-independent by `SeedDeferral.honest_result_indep_of_seed`.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.BlindComparison

/-- The random oracle, instrumented with a flag recording whether `S` has been queried. -/
def tagged (S : Bytes → Prop) [DecidablePred S] :
    QueryImpl HashSpec (StateT (QueryCache HashSpec × Bool) ProbComp) :=
  fun input state => do
    let step ← (randomOracle input).run state.1
    pure (step.1, (step.2, state.2 || decide (S input)))

/-- Two caches agreeing off `S`. -/
def AgreeOff (S : Bytes → Prop) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬ S input → left input = right input

/-- Once set, the flag stays set. -/
theorem flag_persists {α : Type} (S : Bytes → Prop) [DecidablePred S]
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (result : α × QueryCache HashSpec × Bool)
    (hmem : result ∈ support ((simulateQ (tagged S) computation).run (cache, true))) :
    result.2.2 = true := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind input next ih =>
    rw [simulateQ_bind, show simulateQ (tagged S)
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = tagged S input
      from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hflag : step.2.2 = true := by
      have hcopy := hstep
      simp only [tagged, StateT.run] at hcopy
      rw [mem_support_bind_iff] at hcopy
      obtain ⟨inner, -, hinner⟩ := hcopy
      rw [support_pure, Set.mem_singleton_iff] at hinner
      subst hinner
      simp
    rw [show step.2 = (step.2.1, true) from by rw [← hflag]] at hrest
    exact ih step.1 step.2.1 result hrest

/-- The instrumented oracle never fails. -/
theorem tagged_neverFails {α : Type} (S : Bytes → Prop) [DecidablePred S]
    (computation : OracleComp HashSpec α) (state : QueryCache HashSpec × Bool) :
    Pr[⊥ | (simulateQ (tagged S) computation).run state] = 0 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [simulateQ_pure, StateT.run_pure]; simp
  | query_bind input next ih =>
    rw [simulateQ_bind, show simulateQ (tagged S)
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = tagged S input
      from by simp, StateT.run_bind, probFailure_bind_eq_add_tsum]
    have hstepFails : Pr[⊥ | (tagged S input).run state] = 0 := by
      simp [tagged, StateT.run]
    rw [hstepFails, zero_add]
    simp [ih]

/-- Once the flag is set the event is certain. -/
theorem flag_one {α : Type} (S : Bytes → Prop) [DecidablePred S]
    (computation : OracleComp HashSpec α) (cache : QueryCache HashSpec) :
    Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
      (simulateQ (tagged S) computation).run (cache, true)] = 1 :=
  probEvent_eq_one ⟨tagged_neverFails S computation (cache, true),
    fun result hmem => flag_persists S computation cache result hmem⟩

end SlhDsaSecurity.BlindComparison

import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.CanonicalGraph.Programming

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

/-- `AgreeOff` survives a query outside `S`. -/
theorem AgreeOff.cacheQuery {S : Bytes → Prop} {left right : QueryCache HashSpec}
    (hagree : AgreeOff S left right) (input : Bytes) (answer : HashOutput) :
    AgreeOff S (left.cacheQuery input answer) (right.cacheQuery input answer) := by
  intro probe hprobe
  by_cases hsame : probe = input
  · subst hsame
    rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne left answer hsame,
      QueryCache.cacheQuery_of_ne right answer hsame]
    exact hagree probe hprobe

/-- **Two caches agreeing off `S` touch `S` with the same probability.**

The proof is the exactness the route turns on. At a query inside `S` both runs set the flag,
and `flag_one` makes both sides `1` whatever the caches do afterwards — the event is already
decided, so the divergence costs nothing. At a query outside `S` the two caches agree *at that
input*, so the answer distribution is the same and `AgreeOff` survives into the recursion. -/
theorem prob_touched_eq {α : Type} (S : Bytes → Prop) [DecidablePred S]
    (computation : OracleComp HashSpec α) :
    ∀ (left right : QueryCache HashSpec) (flag : Bool), AgreeOff S left right →
      Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
          (simulateQ (tagged S) computation).run (left, flag)] =
        Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
          (simulateQ (tagged S) computation).run (right, flag)] := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro left right flag _
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind input next ih =>
    intro left right flag hagree
    simp only [simulateQ_bind, show simulateQ (tagged S)
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = tagged S input
      from by simp, StateT.run_bind]
    by_cases hmember : S input
    · -- Inside `S`: both runs set the flag, so both sides are already certain.
      have hone : ∀ cache : QueryCache HashSpec,
          Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
            (tagged S input).run (cache, flag) >>= fun step =>
              (simulateQ (tagged S) (next step.1)).run step.2] = 1 := by
        intro cache
        rw [probEvent_bind_eq_tsum]
        have hterm : ∀ step ∈ support ((tagged S input).run (cache, flag)),
            Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
              (simulateQ (tagged S) (next step.1)).run step.2] = 1 := by
          intro step hstep
          have hflag : step.2.2 = true := by
            have hcopy := hstep
            simp only [tagged, StateT.run] at hcopy
            rw [mem_support_bind_iff] at hcopy
            obtain ⟨inner, -, hinner⟩ := hcopy
            rw [support_pure, Set.mem_singleton_iff] at hinner
            subst hinner
            simp [hmember]
          rw [show step.2 = (step.2.1, true) from by rw [← hflag]]
          exact flag_one S (next step.1) step.2.1
        calc ∑' step, Pr[= step | (tagged S input).run (cache, flag)] *
              Pr[fun result : α × QueryCache HashSpec × Bool => result.2.2 = true |
                (simulateQ (tagged S) (next step.1)).run step.2]
            = ∑' step, Pr[= step | (tagged S input).run (cache, flag)] := by
              refine tsum_congr fun step => ?_
              by_cases hmem : step ∈ support ((tagged S input).run (cache, flag))
              · rw [hterm step hmem, mul_one]
              · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          _ = 1 := by
              rw [← probFailure_add_tsum_probOutput ((tagged S input).run (cache, flag))]
              simp [tagged, StateT.run]
      rw [hone left, hone right]
    · -- Outside `S`: the caches agree at this input, so the step is the same.
      have hsame : left input = right input := hagree input hmember
      cases hcached : left input with
      | some cached =>
        have hright : right input = some cached := by rw [← hsame, hcached]
        have hrun : ∀ cache : QueryCache HashSpec, cache input = some cached →
            (tagged S input).run (cache, flag) =
              (pure (cached, (cache, flag || decide (S input))) :
                ProbComp (HashOutput × QueryCache HashSpec × Bool)) := by
          intro cache hcache
          show ((randomOracle input).run cache >>= fun step =>
            pure (step.1, (step.2, flag || decide (S input)))) = _
          rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]
        rw [hrun left hcached, hrun right hright, pure_bind, pure_bind]
        exact ih cached left right _ hagree
      | none =>
        have hright : right input = none := by rw [← hsame, hcached]
        have hrun : ∀ cache : QueryCache HashSpec, cache input = none →
            (tagged S input).run (cache, flag) =
              (fun answer => (answer, (cache.cacheQuery input answer,
                flag || decide (S input)))) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
          intro cache hcache
          show ((randomOracle input).run cache >>= fun step =>
            pure (step.1, (step.2, flag || decide (S input)))) = _
          rw [QueryImpl.withCaching_run_none _ hcache]
          simp only [uniformSampleImpl, bind_map_left, map_eq_bind_pure_comp,
            Function.comp_def, bind_assoc, pure_bind]
        rw [hrun left hcached, hrun right hright]
        rw [bind_map_left, bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        exact tsum_congr fun answer =>
          congrArg _ (ih answer _ _ _ (hagree.cacheQuery input answer))

/-! ## The programmed cache against the blind one

Presampling leaves the run holding `CanonicalGraph.Programming.cacheFrom`: the honest answers,
written at the canonical inputs and nowhere else. The blind cache is the empty one. They
therefore agree everywhere off the canonical inputs, which is exactly the hypothesis
`prob_touched_eq` wants — so the real game and the blind game meet a seed-derived key with the
same probability, and `SeedDeferral.prob_run_meets_honest_key_le` finishes on the blind side.

Nothing is lost in the comparison, which matters because the input half is allotted exactly
`q / 2 ^ 128` and the budget is met with equality. -/

/-- The inputs the programmed cache writes: the canonical ones. -/
def IsCanonicalInput (publicSeed : Digest) (cells : CanonicalGraph.Cells) (input : Bytes) :
    Prop :=
  ∃ parent : CanonicalGraph.StructuralNode,
    input = CanonicalGraph.canonicalInput publicSeed cells parent

/-- **Programming writes only at canonical inputs**, so the result agrees with whatever cache
it started from everywhere else. -/
theorem agreeOff_cacheFrom (publicSeed : Digest) (cells : CanonicalGraph.Cells)
    (outputs : CanonicalGraph.Programming.Outputs) :
    ∀ (parents : List CanonicalGraph.StructuralNode) (cache : QueryCache HashSpec),
      AgreeOff (IsCanonicalInput publicSeed cells)
        (CanonicalGraph.Programming.cacheFrom publicSeed cells outputs parents cache) cache := by
  intro parents
  induction parents with
  | nil => intro cache input _; rfl
  | cons parent parents ih =>
    intro cache input hinput
    rw [CanonicalGraph.Programming.cacheFrom, ih _ input hinput]
    exact QueryCache.cacheQuery_of_ne cache (outputs parent)
      (fun hsame => hinput ⟨parent, hsame⟩)

/-- **The programmed cache agrees with the empty one off the canonical inputs.** -/
theorem agreeOff_cacheFrom_empty (publicSeed : Digest) (cells : CanonicalGraph.Cells)
    (outputs : CanonicalGraph.Programming.Outputs)
    (parents : List CanonicalGraph.StructuralNode) :
    AgreeOff (IsCanonicalInput publicSeed cells)
      (CanonicalGraph.Programming.cacheFrom publicSeed cells outputs parents ∅) ∅ :=
  agreeOff_cacheFrom publicSeed cells outputs parents ∅

end SlhDsaSecurity.BlindComparison

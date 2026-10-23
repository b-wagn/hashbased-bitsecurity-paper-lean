import SlhDsaSecurity.Proof.ShareBound
import SlhDsaSecurity.Proof.VerificationBudget

/-!
# The blind verifier's probes are filed

`visible` reads the open table first and the oracle's cache after it, in the order the blind
router (`route false`) answers. Along a run of world queries the served digests do not move, so
the open table does not either; the cache only grows, and an input the open table lacks stays
lacked. So every answer a blind world step takes is the one `visible` gives at the end of the run,
and replaying a hash computation at the final visible cache consults only inputs the run filed,
each at the digests served when the run began. This holds at any step that routes a hash input
blindly and files it (`RoutesBlind`), whatever else the state carries:

* at the flag-free blind step `ShareBlindFacts.blindStep` (`blind_probes_filed`, and at the
  verifier `blind_verify_probes_filed`);
* at the flagged blind handler, from any flag (`probes_filed`, `verify_probes_filed_any`) — world
  steps never read the flag.

No cold cache is needed for this. The cold cache (`ColdCache`) is the separate fact that a blind
run that ends with the flag down never cached an input of the walk's warm cache.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ShareFiled

open Security CanonicalGraph ShareGame

/-! ## The cold cache -/

/-- **The oracle cache is cold**: it holds no input of the walk's warm cache. -/
def ColdCache (setup : Setup) (state : St) : Prop :=
  ∀ input, state.cache input ≠ none → setup.warm input = none

theorem coldCache_start (setup : Setup) : ColdCache setup St.start := by
  intro input h
  exact absurd rfl h

/-- What a blind routed query does to the cache: nothing, or it caches an input the open table
lacks and the cache did not hold. -/
theorem route_false_cases (setup : Setup) (state : St) (input : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (route false setup state input)) :
    (openAt setup state.served input = some z.1 ∧ z.2 = state) ∨
      (openAt setup state.served input = none ∧ state.cache input = some z.1 ∧ z.2 = state) ∨
        (openAt setup state.served input = none ∧ state.cache input = none ∧
          z.2 = { state with cache := state.cache.cacheQuery input z.1 }) := by
  classical
  unfold route at hz
  rw [if_neg Bool.false_ne_true] at hz
  cases hopen : openAt setup state.served input with
  | some answer =>
    simp only [hopen, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    simp only [hopen, Bool.false_eq_true, false_and, if_false] at hz
    unfold plain at hz
    cases hcached : state.cache input with
    | some answer =>
      simp only [hcached, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    | none =>
      simp only [hcached, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

/-- **A blind routed query that is no sensitive probe keeps the cache cold.** -/
theorem coldCache_route (setup : Setup) (state : St) (input : Bytes)
    (hsens : ¬ Sens setup state.served input) (hcold : ColdCache setup state)
    (z : HashOutput × St) (hz : z ∈ support (route false setup state input)) :
    ColdCache setup z.2 := by
  rcases route_false_cases setup state input z hz with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hopen, -, h⟩
  · rw [h]; exact hcold
  · rw [h]; exact hcold
  · intro other hother
    rw [h] at hother
    by_cases hx : other = input
    · subst hx
      cases hwarm : setup.warm other with
      | none => rfl
      | some answer =>
        exact absurd (ShareUntilBad.sens_of_closed setup state.served other answer hwarm hopen)
          hsens
    · exact hcold other (by simpa [QueryCache.cacheQuery_of_ne _ _ hx] using hother)

theorem prfAt_cache (state : St) (frame : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (prfAt state frame)) : z.2.cache = state.cache ∧ z.2.served = state.served := by
  unfold prfAt at hz
  split at hz
  · rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl⟩
  · rw [mem_support_bind_iff] at hz
    obtain ⟨value, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨rfl, rfl⟩

theorem coldCache_of_cache_eq {setup : Setup} {state state' : St}
    (h : state'.cache = state.cache) (hcold : ColdCache setup state) : ColdCache setup state' := by
  intro input hinput
  rw [h] at hinput
  exact hcold input hinput

open scoped Classical in
/-- **Every blind step that leaves the flag down keeps the cache cold.** -/
theorem coldCache_step (setup : Setup) (queried : ShareSpec.Domain) (state : St × Bool)
    (hcold : ColdCache setup state.1) (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler false setup) queried).run state)) (hflag : z.2.2 = false) :
    ColdCache setup z.2.1 := by
  classical
  obtain ⟨inner, flag⟩ := state
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      exact hcold
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨step, hstep, rfl⟩ := hz
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hflag
      exact coldCache_route setup inner input (fun h => hflag.2.2 (Or.inl h)) hcold step hstep
  · cases hframe : request.frame with
    | none =>
      simp only [handler, StateT.run, hframe, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcold
    | some framed =>
      simp only [handler, StateT.run, hframe, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨seed, hseed, digest, hdigest, rfl⟩ := hz
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hflag
      obtain ⟨hseedCache, hseedServed⟩ := prfAt_cache inner framed seed hseed
      exact coldCache_route setup seed.2 _ (by rw [hseedServed]; exact fun h => hflag.2.2 (Or.inl h))
        (coldCache_of_cache_eq hseedCache hcold) digest hdigest
  · cases drawn with
    | none =>
      simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcold
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [handler, StateT.run] at hz
      split_ifs at hz <;>
      · rw [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact hcold
  · simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hcold

/-- **The flag is sticky**: a step from a raised flag keeps it raised. -/
theorem flag_sticky (lenient : Bool) (setup : Setup) (queried : ShareSpec.Domain)
    (state : St × Bool) (hflag : state.2 = true) (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) queried).run state)) : z.2.2 = true := by
  classical
  obtain ⟨inner, flag⟩ := state
  simp only at hflag
  subst hflag
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      rfl
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨step, -, rfl⟩ := hz
      simp
  · cases hframe : request.frame with
    | none =>
      simp only [handler, StateT.run, hframe, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | some framed =>
      simp only [handler, StateT.run, hframe, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨seed, -, digest, -, rfl⟩ := hz
      simp
  · cases drawn with
    | none =>
      simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [handler, StateT.run] at hz
      split_ifs at hz <;>
      · rw [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
  · simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    simp

/-- **A blind run that ends with the flag down ends with a cold cache**, from a cold start. -/
theorem coldCache_run (setup : Setup) {α : Type} (computation : OracleComp ShareSpec α)
    (state : St × Bool) (hcold : ColdCache setup state.1)
    (z : α × (St × Bool))
    (hz : z ∈ support ((simulateQ (handler false setup) computation).run state))
    (hflag : z.2.2 = false) : ColdCache setup z.2.1 := by
  have key := SignedWatch.run_invariant (handler false setup)
    (fun state : St × Bool => state.2 = true ∨ ColdCache setup state.1)
    (fun queried state hstate step hstep => by
      rcases hstate with hraised | hcold
      · exact Or.inl (flag_sticky false setup queried state hraised step hstep)
      · cases hstepFlag : step.2.2 with
        | true => exact Or.inl rfl
        | false => exact Or.inr (coldCache_step setup queried state hcold step hstep hstepFlag))
    computation state (Or.inr hcold) z hz
  rcases key with hraised | hcold'
  · rw [hflag] at hraised; cases hraised
  · exact hcold'

/-! ## A step that routes blindly and files -/

/-- **The visible cache grows** from one state to the next: every visible entry stays. -/
def Grows (setup : Setup) (old new : St) : Prop :=
  ∀ input value, visible setup old input = some value → visible setup new input = some value

theorem Grows.refl (setup : Setup) (state : St) : Grows setup state state := fun _ _ h => h

theorem Grows.trans {setup : Setup} {first second third : St} (h1 : Grows setup first second)
    (h2 : Grows setup second third) : Grows setup first third :=
  fun x v h => h2 x v (h1 x v h)

/-- **A hash handler that routes blindly and files**, read through a projection to the game's
state: each step answers as the blind router does and files the input at the served digests. -/
def RoutesBlind (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) : Prop :=
  ∀ input state z, z ∈ support ((impl input).run state) →
    ∃ routed ∈ support (route false setup (π state) input), z.1 = routed.1 ∧
      π z.2 = { routed.2 with record := (π state).record ++ [(input, (π state).served)] }

/-- **One blind routed step, filed**: the digests stay, the input is filed at them, the visible
cache grows, and it answers the input as the step did. -/
theorem routed_step (setup : Setup) (state : St) (input : Bytes) (routed : HashOutput × St)
    (hrouted : routed ∈ support (route false setup state input)) :
    let next : St := { routed.2 with record := state.record ++ [(input, state.served)] }
    next.served = state.served ∧ next.record = state.record ++ [(input, state.served)] ∧
      Grows setup state next ∧ visible setup next input = some routed.1 := by
  intro next
  obtain ⟨hserved, -, -⟩ := ShareFlag.route_mem_support false setup state input routed hrouted
  have hserved' : next.served = state.served := hserved
  refine ⟨hserved', rfl, ?_, ?_⟩
  · intro x v hx
    unfold visible at hx ⊢
    rw [hserved']
    cases hopen : openAt setup state.served x with
    | some answer =>
      rw [hopen] at hx
      exact hx
    | none =>
      rw [hopen] at hx
      simp only at hx ⊢
      show routed.2.cache x = some v
      rcases route_false_cases setup state input routed hrouted with
        ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hcached, h⟩
      · rw [h]; exact hx
      · rw [h]; exact hx
      · rw [h]
        by_cases hxi : x = input
        · subst hxi
          rw [hcached] at hx
          cases hx
        · simpa [QueryCache.cacheQuery_of_ne _ _ hxi] using hx
  · unfold visible
    rw [hserved']
    rcases route_false_cases setup state input routed hrouted with
      ⟨hopen, -⟩ | ⟨hopen, hcached, h⟩ | ⟨hopen, -, h⟩
    · rw [hopen]
    · rw [hopen]
      show routed.2.cache input = some routed.1
      rw [h]; exact hcached
    · rw [hopen]
      show routed.2.cache input = some routed.1
      rw [h]; exact QueryCache.cacheQuery_self _ _ _

/-- **One step of a handler that routes blindly and files.** -/
theorem hash_step (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    (input : Bytes) (state : σ) (step : HashOutput × σ)
    (hstep : step ∈ support ((impl input).run state)) :
    (π step.2).served = (π state).served ∧
      (π step.2).record = (π state).record ++ [(input, (π state).served)] ∧
        Grows setup (π state) (π step.2) ∧ visible setup (π step.2) input = some step.1 := by
  obtain ⟨routed, hrouted, hanswer, hnext⟩ := himpl input state step hstep
  rw [hnext, hanswer]
  exact routed_step setup (π state) input routed hrouted

/-- **Along a run of a handler that routes blindly and files**: the digests stay, the record only
grows, and the visible cache grows. -/
theorem hash_run (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (state : σ), ∀ z ∈ support ((simulateQ impl computation).run state),
      (π z.2).served = (π state).served ∧ (π state).record <+: (π z.2).record ∧
        Grows setup (π state) (π z.2) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, List.prefix_refl _, Grows.refl _ _⟩
  | query_bind input next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    obtain ⟨hserved, hrecord, hgrows, -⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨hserved', hprefix', hgrows'⟩ := ih step.1 step.2 z hrest
    refine ⟨hserved'.trans hserved, ?_, hgrows.trans hgrows'⟩
    exact (List.prefix_append _ _).trans (hrecord ▸ hprefix')

/-- **Every probe a replay at the final visible cache consults was filed at the starting
digests**, along a run of a handler that routes blindly and files. -/
theorem probe_filed (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) (probe : Bytes) (final : St)
    (hquery : CacheReplay.QueriesUnder (visible setup final) computation probe) :
    ∀ (state : σ), ∀ z ∈ support ((simulateQ impl computation).run state), π z.2 = final →
      (probe, (π state).served) ∈ final.record := by
  induction hquery with
  | head input next =>
    intro state z hmem hfinal
    rw [simulateQ_bind, show simulateQ impl (query (spec := HashSpec) input) =
        impl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨-, hrecord, -, -⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨-, hprefix, -⟩ := hash_run setup π impl himpl (next step.1) step.2 z hrest
    rw [← hfinal]
    refine hprefix.subset ?_
    rw [hrecord]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  | tail input probe next _ ih =>
    intro state z hmem hfinal
    rw [simulateQ_bind, show simulateQ impl (query (spec := HashSpec) input) =
        impl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨hserved, -, -, hvisible⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨-, -, hgrows⟩ := hash_run setup π impl himpl (next step.1) step.2 z hrest
    have hreplay : CacheReplay.replay (visible setup final) input = step.1 := by
      rw [← hfinal]
      simp [CacheReplay.replay, hgrows input step.1 hvisible]
    rw [← hserved]
    exact ih step.2 z (by rw [hreplay]; exact hrest) hfinal

/-- **A world run of a lifted hash computation** at a handler whose hash steps route blindly and
file keeps the digests, and every probe a replay of the computation at the final visible cache
consults is filed in the record at the starting digests. -/
theorem probes_filed_of (setup : Setup) {σ : Type} (π : σ → St)
    (coin : QueryImpl unifSpec (StateT σ ProbComp))
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) (state : σ) (z : α × σ)
    (hz : z ∈ support ((simulateQ (coin + impl)
      (OracleComp.liftComp computation OracleWorld)).run state)) :
    (π z.2).served = (π state).served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup (π z.2)) computation probe →
        (probe, (π state).served) ∈ (π z.2).record := by
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  exact ⟨(hash_run setup π impl himpl computation state z hz).1, fun probe hprobe =>
    probe_filed setup π impl himpl computation probe _ hprobe state z hz rfl⟩

/-! ## At the flag-free blind step -/

/-- **The flag-free blind step, read at the verifier's oracles.** -/
noncomputable def blindWorldImpl (setup : Setup) : QueryImpl OracleWorld (StateT St ProbComp) :=
  QueryImpl.compose (ShareBlindFacts.blindStep setup) fun world =>
    (query (spec := ShareSpec) (worldQuery world) : OracleComp ShareSpec (OracleWorld.Range world))

theorem blindWorldImpl_run (setup : Setup) (world : OracleWorld.Domain) (state : St) :
    ((blindWorldImpl setup) world).run state =
      ((ShareBlindFacts.blindStep setup) (worldQuery world)).run state := by
  simp only [blindWorldImpl, QueryImpl.apply_compose, HasQuery.instOfMonadLift_query]
  erw [simulateQ_spec_query]
  rfl

theorem blindStep_verifyShare_run (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (state : St) :
    (simulateQ (ShareBlindFacts.blindStep setup) (verifyShare pk forgery)).run state =
      (simulateQ (blindWorldImpl setup)
        (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message forgery.signature)).run
          state := by
  rw [verifyShare, ← QueryImpl.simulateQ_compose]
  rfl

/-- The flag-free blind step at a hash input. -/
noncomputable def blindHashImpl (setup : Setup) : QueryImpl HashSpec (StateT St ProbComp) :=
  fun input => blindWorldImpl setup (Sum.inr input)

/-- The flag-free blind step at a coin. -/
noncomputable def blindCoinImpl (setup : Setup) : QueryImpl unifSpec (StateT St ProbComp) :=
  fun coin => blindWorldImpl setup (Sum.inl coin)

theorem blindWorldImpl_eq_add (setup : Setup) :
    blindWorldImpl setup = blindCoinImpl setup + blindHashImpl setup := by
  funext queried
  rcases queried with coin | input <;> rfl

theorem blindHashImpl_run (setup : Setup) (input : Bytes) (state : St) :
    (blindHashImpl setup input).run state = (do
      let step ← route false setup state input
      pure (step.1, { step.2 with record := state.record ++ [(input, state.served)] })) := by
  show ((blindWorldImpl setup) (Sum.inr input)).run state = _
  rw [blindWorldImpl_run]
  rfl

theorem routesBlind_blindHashImpl (setup : Setup) :
    RoutesBlind setup id (blindHashImpl setup) := by
  intro input state z hz
  rw [blindHashImpl_run, mem_support_bind_iff] at hz
  obtain ⟨routed, hrouted, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨routed, hrouted, rfl, rfl⟩

/-- **At the flag-free blind step**: a world run of a lifted hash computation keeps the digests,
and every probe a replay of the computation at the final visible cache consults is filed in the
record at the starting digests. -/
theorem blind_probes_filed (setup : Setup) {α : Type} (computation : OracleComp HashSpec α)
    (p : St) (z : α × St)
    (hz : z ∈ support ((simulateQ (blindWorldImpl setup)
      (OracleComp.liftComp computation OracleWorld)).run p)) :
    z.2.served = p.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2) computation probe →
        (probe, p.served) ∈ z.2.record := by
  rw [blindWorldImpl_eq_add] at hz
  exact probes_filed_of setup id (blindCoinImpl setup) (blindHashImpl setup)
    (routesBlind_blindHashImpl setup) computation p z hz

/-- **At the flag-free blind step's verifier**, run on the world. -/
theorem blind_verify_probes_filed (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St) (z : Bool × St)
    (hz : z ∈ support ((simulateQ (blindWorldImpl setup)
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run p)) :
    z.2.served = p.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.served) ∈ z.2.record := by
  rw [VerificationBudget.verify_lift] at hz
  exact blind_probes_filed setup _ p z hz

/-- **At the flag-free blind step's verifier step** (`ShareGame.verifyShare`). -/
theorem blind_verifyShare_probes_filed (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (p : St) (z : Bool × St)
    (hz : z ∈ support ((simulateQ (ShareBlindFacts.blindStep setup)
      (verifyShare pk forgery)).run p)) :
    z.2.served = p.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2)
          (Scheme.verify (m := OracleComp HashSpec) pk forgery.message forgery.signature) probe →
        (probe, p.served) ∈ z.2.record := by
  rw [blindStep_verifyShare_run] at hz
  exact blind_verify_probes_filed setup pk forgery.message forgery.signature p z hz

/-! ## At the flagged blind handler, from any flag -/

theorem worldImpl_run (lenient : Bool) (setup : Setup) (world : OracleWorld.Domain)
    (p : St × Bool) :
    ((ShareBound.worldImpl lenient setup) world).run p =
      ((handler lenient setup) (worldQuery world)).run p := by
  simp only [ShareBound.worldImpl, QueryImpl.apply_compose, HasQuery.instOfMonadLift_query]
  erw [simulateQ_spec_query]
  rfl

/-- The blind world handler at a hash input. -/
noncomputable def hashImpl (setup : Setup) : QueryImpl HashSpec (StateT (St × Bool) ProbComp) :=
  fun input => ShareBound.worldImpl false setup (Sum.inr input)

/-- The blind world handler at a coin. -/
noncomputable def coinImpl (setup : Setup) : QueryImpl unifSpec (StateT (St × Bool) ProbComp) :=
  fun coin => ShareBound.worldImpl false setup (Sum.inl coin)

theorem worldImpl_eq_add (setup : Setup) :
    ShareBound.worldImpl false setup = coinImpl setup + hashImpl setup := by
  funext queried
  rcases queried with coin | input <;> rfl

open scoped Classical in
theorem hashImpl_run (setup : Setup) (input : Bytes) (p : St × Bool) :
    (hashImpl setup input).run p = (do
      let step ← route false setup p.1 input
      pure (step.1, ({ step.2 with record := p.1.record ++ [(input, p.1.served)] },
        p.2 || decide (¬ setup.Good ∨ Guess setup p.1.served input)))) := by
  show ((ShareBound.worldImpl false setup) (Sum.inr input)).run p = _
  rw [worldImpl_run]
  rfl

theorem routesBlind_hashImpl (setup : Setup) :
    RoutesBlind setup Prod.fst (hashImpl setup) := by
  classical
  intro input state z hz
  rw [hashImpl_run, mem_support_bind_iff] at hz
  obtain ⟨routed, hrouted, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨routed, hrouted, rfl, rfl⟩

/-- **A blind world run of a lifted hash computation**, from any flag, keeps the digests, and
every probe a replay of the computation at the final visible cache consults is filed in the
record at the starting digests. -/
theorem probes_filed {α : Type} (setup : Setup) (computation : OracleComp HashSpec α)
    (p : St × Bool) (z : α × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (OracleComp.liftComp computation OracleWorld)).run p)) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1) computation probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [worldImpl_eq_add] at hz
  exact probes_filed_of setup Prod.fst (coinImpl setup) (hashImpl setup)
    (routesBlind_hashImpl setup) computation p z hz

/-- **At the verifier, as a hash computation lifted to the world.** -/
theorem verify_probes_filed_lift (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St × Bool) (z : Bool × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (OracleComp.liftComp (Scheme.verify (m := OracleComp HashSpec) pk request wire)
        OracleWorld)).run p)) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.1.served) ∈ z.2.1.record :=
  probes_filed setup _ p z hz

/-- **At the verifier, run on the world** as the share game runs it, from any flag. -/
theorem verify_probes_filed_any (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St × Bool) (w : Bool × (St × Bool))
    (hw : w ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run p)) :
    w.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup w.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.1.served) ∈ w.2.1.record := by
  rw [VerificationBudget.verify_lift] at hw
  exact probes_filed setup _ p w hw

/-- **At the share game's verifier step** (`ShareGame.verifyShare`), from any flag. -/
theorem verifyShare_probes_filed (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (p : St × Bool) (z : Bool × (St × Bool))
    (hz : z ∈ support ((simulateQ (handler false setup) (verifyShare pk forgery)).run p)) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk forgery.message forgery.signature) probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [ShareBound.verifyShare_run] at hz
  exact verify_probes_filed_any setup pk forgery.message forgery.signature p z hz

end SlhDsaSecurity.ShareFiled

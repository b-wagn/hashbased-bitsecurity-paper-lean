import SlhDsaSecurity.Proof.ShareBound
import SlhDsaSecurity.Proof.VerificationBudget

/-!
# The blind verifier's probes are filed

On a blind run that never raises the flag, the oracle cache only ever receives inputs off the
walk's warm cache: a canonical input the open table lacks is a sensitive probe
(`ShareUntilBad.sens_of_closed`), and a sensitive probe raises the flag. So the cache and the
open table never disagree (`ColdCache`), and every answer the run takes is the one `visible`
replays at its end. Replaying a hash computation at the final visible cache therefore consults
only inputs the run filed, each at the digests served when the run began
(`probes_filed`, and at the verifier `verify_probes_filed`).
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

/-! ## One blind world hash step -/

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

/-- **The visible cache grows** from one state to the next: every visible entry stays. -/
def Grows (setup : Setup) (old new : St) : Prop :=
  ∀ input value, visible setup old input = some value → visible setup new input = some value

theorem Grows.refl (setup : Setup) (state : St) : Grows setup state state := fun _ _ h => h

theorem Grows.trans {setup : Setup} {first second third : St} (h1 : Grows setup first second)
    (h2 : Grows setup second third) : Grows setup first third :=
  fun x v h => h2 x v (h1 x v h)

/-- **One blind hash step that leaves the flag down**: the flag was down, the digests stay, the
input is filed at them, the cache stays cold, the visible cache grows and answers the input as the
step did. -/
theorem hash_step (setup : Setup) (input : Bytes) (p : St × Bool) (hcold : ColdCache setup p.1)
    (step : HashOutput × (St × Bool)) (hstep : step ∈ support ((hashImpl setup input).run p))
    (hflag : step.2.2 = false) :
    p.2 = false ∧ step.2.1.served = p.1.served ∧
      step.2.1.record = p.1.record ++ [(input, p.1.served)] ∧ ColdCache setup step.2.1 ∧
        Grows setup p.1 step.2.1 ∧ visible setup step.2.1 input = some step.1 := by
  classical
  obtain ⟨inner, flag⟩ := p
  rw [hashImpl_run, mem_support_bind_iff] at hstep
  obtain ⟨routed, hrouted, hz⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_or] at hflag
  obtain ⟨hserved, -, -⟩ := ShareFlag.route_mem_support false setup inner input routed hrouted
  refine ⟨hflag.1, hserved, rfl,
    coldCache_route setup inner input (fun h => hflag.2.2 (Or.inl h)) hcold routed hrouted, ?_, ?_⟩
  · intro x v hx
    unfold visible at hx ⊢
    simp only [hserved]
    rcases route_false_cases setup inner input routed hrouted with
      ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨hopen, hcached, h⟩
    · rw [h]; exact hx
    · rw [h]; exact hx
    · rw [h]
      by_cases hxi : x = input
      · subst hxi
        rw [hcached, hopen] at hx
        cases hx
      · simpa [QueryCache.cacheQuery_of_ne _ _ hxi] using hx
  · unfold visible
    simp only [hserved]
    rcases route_false_cases setup inner input routed hrouted with
      ⟨hopen, h⟩ | ⟨-, hcached, h⟩ | ⟨-, -, h⟩
    · rw [h]
      have hwarm := ShareUntilBad.openAt_le_warm setup inner.served input routed.1 hopen
      have hnone : inner.cache input = none := by
        by_contra hne
        rw [hcold input hne] at hwarm
        cases hwarm
      simp [hnone, hopen]
    · rw [h]; simp [hcached]
    · rw [h]; simp [QueryCache.cacheQuery_self]

/-- A blind hash step that ends with the flag down began with it down. -/
theorem hash_flag_down (setup : Setup) (input : Bytes) (p : St × Bool)
    (step : HashOutput × (St × Bool)) (hstep : step ∈ support ((hashImpl setup input).run p))
    (hflag : step.2.2 = false) : p.2 = false := by
  obtain ⟨inner, flag⟩ := p
  rw [hashImpl_run, mem_support_bind_iff] at hstep
  obtain ⟨routed, -, hz⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp only [Bool.or_eq_false_iff] at hflag
  exact hflag.1

/-- A blind hash run that ends with the flag down began with it down. -/
theorem run_flag_down {α : Type} (setup : Setup) (computation : OracleComp HashSpec α) :
    ∀ (p : St × Bool), ∀ z ∈ support ((simulateQ (hashImpl setup) computation).run p),
      z.2.2 = false → p.2 = false := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro p z hz hflag
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hflag
  | query_bind input next ih =>
    intro p z hz hflag
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact hash_flag_down setup input p step hstep (ih step.1 step.2 z hrest hflag)

/-- **Along a blind hash run that ends with the flag down**: the digests stay, the record only
grows, the cache stays cold, and the visible cache grows. -/
theorem hash_run {α : Type} (setup : Setup) (computation : OracleComp HashSpec α) :
    ∀ (p : St × Bool), ColdCache setup p.1 →
      ∀ z ∈ support ((simulateQ (hashImpl setup) computation).run p), z.2.2 = false →
        z.2.1.served = p.1.served ∧ p.1.record <+: z.2.1.record ∧
          ColdCache setup z.2.1 ∧ Grows setup p.1 z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro p hcold z hz hflag
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, List.prefix_refl _, hcold, Grows.refl _ _⟩
  | query_bind input next ih =>
    intro p hcold z hz hflag
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    have hstepFlag := run_flag_down setup (next step.1) step.2 z hrest hflag
    obtain ⟨-, hserved, hrecord, hcold', hgrows, -⟩ :=
      hash_step setup input p hcold step hstep hstepFlag
    obtain ⟨hserved', hprefix', hcold'', hgrows'⟩ := ih step.1 step.2 hcold' z hrest hflag
    refine ⟨hserved'.trans hserved, ?_, hcold'', hgrows.trans hgrows'⟩
    exact (List.prefix_append _ _).trans (hrecord ▸ hprefix')

/-! ## The filed probes -/

/-- **Every probe a replay at the final visible cache consults was filed at the starting
digests**, along a blind hash run that ends with the flag down. -/
theorem probe_filed {α : Type} (setup : Setup) (computation : OracleComp HashSpec α)
    (probe : Bytes) (final : St)
    (hquery : CacheReplay.QueriesUnder (visible setup final) computation probe) :
    ∀ (p : St × Bool), ColdCache setup p.1 → ∀ (result : α),
      (result, (final, false)) ∈ support ((simulateQ (hashImpl setup) computation).run p) →
        (probe, p.1.served) ∈ final.record := by
  induction hquery with
  | head input next =>
    intro p hcold result hmem
    rw [simulateQ_bind, show simulateQ (hashImpl setup) (query (spec := HashSpec) input) =
        hashImpl setup input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hstepFlag := run_flag_down setup (next step.1) step.2 _ hrest rfl
    obtain ⟨-, -, hrecord, hcold', -, -⟩ := hash_step setup input p hcold step hstep hstepFlag
    obtain ⟨-, hprefix, -, -⟩ := hash_run setup (next step.1) step.2 hcold' _ hrest rfl
    refine hprefix.subset ?_
    rw [hrecord]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  | tail input probe next _ ih =>
    intro p hcold result hmem
    rw [simulateQ_bind, show simulateQ (hashImpl setup) (query (spec := HashSpec) input) =
        hashImpl setup input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hstepFlag := run_flag_down setup (next step.1) step.2 _ hrest rfl
    obtain ⟨-, hserved, -, hcold', -, hvisible⟩ :=
      hash_step setup input p hcold step hstep hstepFlag
    obtain ⟨-, -, -, hgrows⟩ := hash_run setup (next step.1) step.2 hcold' _ hrest rfl
    have hreplay : CacheReplay.replay (visible setup final) input = step.1 := by
      simp [CacheReplay.replay, hgrows input step.1 hvisible]
    rw [← hserved]
    exact ih step.2 hcold' result (by rw [hreplay]; exact hrest)

/-- **A blind world run of a lifted hash computation that ends with the flag down** keeps the
digests, and every probe a replay of the computation at the final visible cache consults is
filed in the record at the starting digests. -/
theorem probes_filed {α : Type} (setup : Setup) (computation : OracleComp HashSpec α)
    (p : St × Bool) (hcold : ColdCache setup p.1) (z : α × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (OracleComp.liftComp computation OracleWorld)).run p))
    (hflag : z.2.2 = false) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1) computation probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [worldImpl_eq_add, QueryImpl.simulateQ_add_liftComp_right] at hz
  obtain ⟨result, final, flag⟩ := z
  simp only at hflag
  subst hflag
  refine ⟨(hash_run setup computation p hcold _ hz rfl).1, fun probe hprobe => ?_⟩
  exact probe_filed setup computation probe final hprobe p hcold result hz

/-- **At the verifier, as a hash computation lifted to the world.** -/
theorem verify_probes_filed_lift (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St × Bool) (hcold : ColdCache setup p.1) (z : Bool × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (OracleComp.liftComp (Scheme.verify (m := OracleComp HashSpec) pk request wire)
        OracleWorld)).run p))
    (hflag : z.2.2 = false) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.1.served) ∈ z.2.1.record :=
  probes_filed setup _ p hcold z hz hflag

/-- **At the verifier, run on the world** as the share game runs it. -/
theorem verify_probes_filed (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St × Bool) (hcold : ColdCache setup p.1) (z : Bool × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run p))
    (hflag : z.2.2 = false) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [VerificationBudget.verify_lift] at hz
  exact probes_filed setup _ p hcold z hz hflag

/-- **At the share game's verifier step** (`ShareGame.verifyShare`). -/
theorem verifyShare_probes_filed (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (p : St × Bool) (hcold : ColdCache setup p.1) (z : Bool × (St × Bool))
    (hz : z ∈ support ((simulateQ (handler false setup) (verifyShare pk forgery)).run p))
    (hflag : z.2.2 = false) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk forgery.message forgery.signature) probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [ShareBound.verifyShare_run] at hz
  exact verify_probes_filed setup pk forgery.message forgery.signature p hcold z hz hflag

end SlhDsaSecurity.ShareFiled

import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.RecordedBudget

/-!
# The budget, carried to the lazy presentation

`RecordedBudget` bounds what the game charges on a run of the shared oracle. The charge of
`SensitiveQuery` consumes a run of `OpenCache.lazyProgram`, whose state records each probe with
the cache it was issued against. The two presentations record different things, and the gap is
not closed by making the recordings agree in type: one exists to be charged, the other to be
counted.

What closes it is that the lazy handler never answers anything the shared oracle could not have
answered. At a cached input both reply from the cache; at an input the walk's table answers, the
lazy handler replies with a value the shared oracle draws with positive probability; everywhere
else both draw. So every run of the lazy presentation is a run of the shared oracle, and every
property the budget establishes with probability one transfers to it unchanged — in particular
the bound on `Outcome.counts.work`, which is the quantity the recorded game's cardinality bound
is stated against.

`mem_support_simulateQ_of_step` is the transfer, stated for any two handlers related by a
relation on their states that each step preserves. It is a forward simulation on supports, not a
comparison of laws: the lazy run's law is *not* the shared oracle's, since the table fixes
answers the oracle would draw. Only the support is contained, and only the support is needed,
because a budget that holds with probability one holds at every supported result.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.LazyBudget

open Security OpenCache CanonicalGraph

/-! ## Forward simulation on supports

Two handlers whose states are related by a relation each step preserves — every step of the
first having a step of the second that returns the same answer and preserves the relation — give
runs whose supports are related the same way. -/

/-- **A forward simulation carries supports.** -/
theorem mem_support_simulateQ_of_step {ι : Type} {spec : OracleSpec ι} {σ τ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (base : QueryImpl spec (StateT τ ProbComp))
    (Agrees : σ → τ → Prop)
    (hstep : ∀ (t : spec.Domain) (s : σ) (u : τ), Agrees s u →
      ∀ z ∈ support ((impl t).run s),
        ∃ w ∈ support ((base t).run u), w.1 = z.1 ∧ Agrees z.2 w.2)
    {α : Type} (computation : OracleComp spec α) :
    ∀ (s : σ) (u : τ), Agrees s u →
      ∀ z ∈ support ((simulateQ impl computation).run s),
        ∃ w ∈ support ((simulateQ base computation).run u), w.1 = z.1 ∧ Agrees z.2 w.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro s u hagree z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    refine ⟨(value, u), ?_, ?_, ?_⟩
    · rw [simulateQ_pure, StateT.run_pure, support_pure]
      rfl
    · rw [hz]
    · rw [hz]
      exact hagree
  | query_bind t next ih =>
    intro s u hagree z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstepmem, hrest⟩ := hz
    obtain ⟨w, hw, hanswer, hrelate⟩ := hstep t s u hagree step hstepmem
    obtain ⟨final, hfinal, hvalue, hstate⟩ := ih step.1 step.2 w.2 hrelate z hrest
    refine ⟨final, ?_, hvalue, hstate⟩
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    exact ⟨w, hw, by rw [hanswer]; exact hfinal⟩

/-! ## The lazy handler answers only what the shared oracle could

The handler's reply to a hash query, with the bookkeeping stripped off, so that the comparison
with the shared oracle is between two computations of the same clean type. Spelling it out is
what lets the step below be read off: a cached input is answered from the cache on both sides, an
input the table answers is answered with a value the oracle draws with positive probability, and
everything else is drawn on both sides. -/

open scoped Classical in
/-- The handler's reply to a hash query: the cache, else the table, else a fresh draw. -/
noncomputable def lazyAnswer (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) (input : Bytes)
    (carrier : HandlerCarrier.State) :
    ProbComp (HashOutput × HandlerCarrier.State) :=
  match carrier.cache input with
  | some cached => pure (cached, carrier)
  | none =>
    match openCache publicSeed (availableAt carrier) table input with
    | some answer => pure (answer, HandlerCarrier.cacheAnswer carrier input answer)
    | none =>
      (fun answer => (answer, HandlerCarrier.cacheAnswer carrier input answer)) <$>
        ($ᵗ HashOutput : ProbComp _)

open scoped Classical in
theorem lazyProgram_run_hash (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) (input : Bytes)
    (state : HandlerState) :
    ((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state =
      lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (HashOutput × HandlerState)) := rfl

open scoped Classical in
/-- **Every reply the handler gives is one the shared oracle gives.** -/
theorem lazyAnswer_mem_randomOracle (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) (input : Bytes)
    (carrier : HandlerCarrier.State) (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    (step.1, step.2.cache) ∈ support ((randomOracle input).run carrier.cache) := by
  classical
  rw [lazyAnswer] at hstep
  cases hcached : carrier.cache input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hstep
    rw [QueryImpl.withCaching_run_some _ hcached, support_pure, Set.mem_singleton_iff]
    rw [show step.1 = cached from by rw [hstep], show step.2 = carrier from by rw [hstep]]
  | none =>
    rw [QueryImpl.withCaching_run_none _ hcached, support_map]
    rw [hcached] at hstep
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hstep
      refine ⟨answer, mem_support_uniformSample _, ?_⟩
      rw [show step.1 = answer from by rw [hstep],
        show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [hstep]]
      rfl
    | none =>
      rw [hopen, support_map] at hstep
      obtain ⟨answer, hanswer, heq⟩ := hstep
      refine ⟨answer, hanswer, ?_⟩
      rw [show step.1 = answer from by rw [← heq],
        show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [← heq]]
      rfl

open scoped Classical in
/-- The hash half of the step, at the clean type. -/
theorem lazyProgram_hash_mem_randomOracle (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) (input : Bytes)
    (state : HandlerState) (z : HashOutput × HandlerState)
    (hz : z ∈ support (((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state)) :
    (z.1, z.2.1.cache) ∈ support ((randomOracle input).run state.1.cache) := by
  have hbind : z ∈ support
      (lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (HashOutput × HandlerState))) := hz
  rw [mem_support_bind_iff] at hbind
  obtain ⟨step, hstep, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [show z.1 = step.1 from by rw [hpure], show z.2.1 = step.2 from by rw [hpure]]
  exact lazyAnswer_mem_randomOracle publicSeed availableAt table input state.1 step hstep

/-- **One step of the lazy handler is one step of the shared oracle.** -/
theorem lazyProgram_step_mem_rom (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (z : OracleWorld.Range queried × HandlerState)
    (hz : z ∈ support (((lazyProgram publicSeed availableAt table) queried).run state)) :
    (z.1, z.2.1.cache) ∈ support ((KeygenUniform.rom queried).run state.1.cache) := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hz
    obtain ⟨value, -, hpure⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show z.1 = value from by rw [hpure], show z.2 = state from by rw [hpure]]
    simp only [KeygenUniform.rom, Xmss.RandomOracleModel.impl, unifFwdImpl,
      QueryImpl.liftTarget, QueryImpl.add_apply_inl, HasQuery.toQueryImpl]
    simp
    exact Set.mem_range_self (f := fun a => (a, state.1.cache)) value
  · exact lazyProgram_hash_mem_randomOracle publicSeed availableAt table input state z hz

/-- **A run of the lazy presentation is a run of the shared oracle.** -/
theorem mem_support_rom_of_lazy (publicSeed : Digest)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    {α : Type} (computation : OracleComp OracleWorld α) (state : HandlerState)
    (z : α × HandlerState)
    (hz : z ∈ support
      ((simulateQ (lazyProgram publicSeed availableAt table) computation).run state)) :
    (z.1, z.2.1.cache) ∈ support
      ((simulateQ KeygenUniform.rom computation).run state.1.cache) := by
  obtain ⟨w, hw, hvalue, hstate⟩ :=
    mem_support_simulateQ_of_step (lazyProgram publicSeed availableAt table)
      KeygenUniform.rom (fun s u => s.1.cache = u)
      (fun queried s u hagree y hy =>
        ⟨(y.1, y.2.1.cache), hagree ▸ lazyProgram_step_mem_rom publicSeed availableAt table
          queried s y hy, rfl, rfl⟩)
      computation state state.1.cache rfl z hz
  rw [show (z.1, z.2.1.cache) = w from Prod.ext hvalue.symm hstate]
  exact hw

/-! ## The budget at the lazy presentation

The budget is a property that holds at every supported result of the shared oracle's run, so
containment of supports delivers it to the lazy presentation without a probabilistic step. What
it bounds is `Outcome.counts.work`, which the stripping surgery leaves untouched and which the
handler, being a handler, does not touch either. -/

attribute [local irreducible] StrippedGame.strippedAfterSeeds WarmedGame.afterSeeds
  Scheme.verify Scheme.keygenInternal Security.countQueries OpenCache.lazyProgram

end SlhDsaSecurity.LazyBudget

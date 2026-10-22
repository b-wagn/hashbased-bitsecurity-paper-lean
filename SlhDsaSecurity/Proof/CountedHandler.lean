import SlhDsaSecurity.Proof.ServedAgreement
import SlhDsaSecurity.Proof.ServingForget
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.WriterState

/-!
# A handler that counts, and why the tail needs one

`FusedCoverage.fusedTail` gets its hash count from `countAllHashes` wrapped around the whole
game. That works because the game is a single `OracleComp OracleWorld`. **A bracketed game is
not one**: its adversary phase lives at `OracleWorld + SigningSpec` and is only assembled by
`FusedGame.run_afterSeeds_split`, so there is no computation for `countAllHashes` to wrap.

Every hash query of every phase passes through the outer handler, so the count belongs in the
handler's state. `withCount` puts it there, at `HandlerCarrier.State × (τ × Nat)` — the carrier
stays first, which is the only thing `ServedAgreement.Files` looks at, so the interface survives
the wrapping with `τ` widened and nothing else moved.

**That the interface survives is a fact about it, not a coincidence.** `Files.queryStep` for a
wrapped handler has to be rebuilt from the step facts of the handler underneath, and a run fact
will not rebuild it — which is why `stepGrows` and `stepFraming` are fields. An interface that
cannot be transported through a wrapper is under-specified, and trying to wrap it is how you
find out.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CountedHandler

open Security HandlerCarrier ServedAgreement

variable (pk : PublicKey) {τ : Type}

/-- A handler with a hash counter beside its carrier. -/
noncomputable def withCount
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)) :
    QueryImpl OracleWorld (StateT (HandlerCarrier.State × (τ × Nat)) ProbComp) :=
  fun queried state => do
    let step ← (impl queried).run (state.1, state.2.1)
    pure (step.1, (step.2.1, (step.2.2, state.2.2 + hashCost queried)))

theorem withCount_run (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Nat)) :
    ((withCount impl) queried).run state =
      (impl queried).run (state.1, state.2.1) >>= fun step =>
        (pure (step.1, (step.2.1, (step.2.2, state.2.2 + hashCost queried))) :
          ProbComp (OracleWorld.Range queried × (HandlerCarrier.State × (τ × Nat)))) := rfl

/-- **A step of the counted handler is a step of the handler, with the counter bumped.**

The carried component comes back too, and not only the carrier. The counter wraps a state whose
other half is the handler's own — two recordings, for the recorder — and a consumer reasoning
about *that* half cannot see through the wrapper without it. It is free from the same hypothesis
the carrier's equality comes from. -/
theorem withCount_step
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Nat))
    (step : OracleWorld.Range queried × (HandlerCarrier.State × (τ × Nat)))
    (hstep : step ∈ support (((withCount impl) queried).run state)) :
    ∃ inner : OracleWorld.Range queried × (HandlerCarrier.State × τ),
      inner ∈ support ((impl queried).run (state.1, state.2.1)) ∧
        step.1 = inner.1 ∧ step.2.1 = inner.2.1 ∧ step.2.2.1 = inner.2.2 := by
  rw [withCount_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨inner, hinner, by rw [hpure], by rw [hpure], by rw [hpure]⟩

/-! ## The same wrapper, at whatever the extra component is

The counter is one instance of a wrapper that carries **some** extra component beside the
handler's own state and updates it per query, without ever reading or writing the carrier. The
cost writer a counted computation threads is another. Both ask the interface the same question
and get the same answer, so the transport is stated once here and the counter is its instance.

`withCount` is unchanged — same name, same type, same definition — so nothing downstream moves;
what changes is that its transport is now a corollary rather than eighty lines of its own.

**Two instances is what makes this a fact rather than a guess.** A transport generalised with
one instance is a prediction about the next one; with two in hand it is a statement about what
the wrapper actually needs, which is: the carrier's half untouched and the handler's own half
returned. -/

/-- A handler with some extra component beside its state, updated per query. -/
noncomputable def withExtra {ω : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω) :
    QueryImpl OracleWorld (StateT (HandlerCarrier.State × (τ × ω)) ProbComp) :=
  fun queried state => do
    let step ← (impl queried).run (state.1, state.2.1)
    pure (step.1, (step.2.1, (step.2.2, update queried state.2.2)))

theorem withExtra_run {ω : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × ω)) :
    ((withExtra impl update) queried).run state =
      (impl queried).run (state.1, state.2.1) >>= fun step =>
        (pure (step.1, (step.2.1, (step.2.2, update queried state.2.2))) :
          ProbComp (OracleWorld.Range queried × (HandlerCarrier.State × (τ × ω)))) := rfl

/-- **A step of the wrapped handler is a step of the handler, with the extra component
updated.** -/
theorem withExtra_step {ω : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × ω))
    (step : OracleWorld.Range queried × (HandlerCarrier.State × (τ × ω)))
    (hstep : step ∈ support (((withExtra impl update) queried).run state)) :
    ∃ inner : OracleWorld.Range queried × (HandlerCarrier.State × τ),
      inner ∈ support ((impl queried).run (state.1, state.2.1)) ∧
        step.1 = inner.1 ∧ step.2.1 = inner.2.1 ∧ step.2.2.1 = inner.2.2 := by
  rw [withExtra_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact ⟨inner, hinner, by rw [hpure], by rw [hpure], by rw [hpure]⟩

/-! ## The cost writer, as an extra

A computation that counts its own queries threads a writer **inside** itself, and
`WriterState.run_simulateQ_withAddCost` fuses that into the handler as `withAddCost`.
`WriterState.toStateful` then moves the accumulator from the writer into the state — but it puts
it **first**, and `ServedAgreement.Files` reads the carrier first. Same data, wrong association,
and the interface cannot see through it.

This is that reassociation, and it is all that stands between a cost-counted run and the
transport above. It is stated at this one pairing rather than as a general relabelling because
there is one instance of it: generalise when the second exists.

What made it fight was not the content. `run_withAddCost_apply` is stated at the handler and
this proof has a state in hand, so nothing rewrote until the same fact was named one level
down, as `WriterState.run_withAddCost_run`.

It is now `run_reencode` at one encoding, the induction having moved there once the flag turned
out to need the same thing. -/

/-- **A wrapper that is `withExtra` at a different tupling is `withExtra`'s run, re-encoded.**

Two wrappers in this development put the carrier somewhere other than first — the cost writer's
`toStateful`, which puts its accumulator before it, and `OpenCache.withFlag`, which puts its
flag after. Both are `withExtra` up to how the state is tupled, and `ServedAgreement.Files`
reads the carrier first, so neither can be used through the interface until it is re-encoded.

This is that re-encoding, from the step to the run. Everything it needs is the step relation,
because the carrier moves the same way at every query. -/
theorem run_reencode {ω σ : Type}
    (handler : QueryImpl OracleWorld (StateT σ ProbComp))
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (encode : σ → HandlerCarrier.State × (τ × ω))
    (hstep : ∀ (queried : OracleWorld.Domain) (state : σ),
      (fun p : OracleWorld.Range queried × σ => (p.1, encode p.2)) <$>
          (handler queried).run state =
        ((withExtra impl update) queried).run (encode state))
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : σ,
      (fun p : α × σ => (p.1, encode p.2)) <$> (simulateQ handler computation).run state =
        (simulateQ (withExtra impl update) computation).run (encode state) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ← hstep queried state,
      bind_map_left, map_eq_bind_pure_comp, bind_assoc]
    refine congrArg (Bind.bind ((handler queried).run state)) (funext fun step => ?_)
    exact ih step.1 step.2

/-- **The flag is an extra too**, carried untouched. `OpenCache.withFlag` puts it after the
handler's state where `withExtra` puts it after the handler's own half; that is the whole
difference, and `run_reencode` is all it takes. -/
theorem run_withFlag_withExtra
    (impl : QueryImpl OracleWorld (StateT OpenCache.HandlerState ProbComp))
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : OpenCache.HandlerState × Bool,
      (fun p : α × (OpenCache.HandlerState × Bool) =>
          (p.1, (p.2.1.1, (p.2.1.2, p.2.2)))) <$>
        (simulateQ (OpenCache.withFlag impl) computation).run state =
      (simulateQ (withExtra impl (fun _ flag => flag)) computation).run
        (state.1.1, (state.1.2, state.2)) :=
  run_reencode (OpenCache.withFlag impl) impl (fun _ flag => flag)
    (fun p => (p.1.1, (p.1.2, p.2)))
    (fun queried st => by
      rw [OpenCache.withFlag_run, withExtra_run, map_eq_bind_pure_comp, bind_assoc]
      exact congrArg (Bind.bind ((impl queried).run st.1))
        (funext fun step => by rw [pure_bind]; rfl))
    computation

theorem run_toStateful_withAddCost {ω : Type} [AddCommMonoid ω]
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (cost : OracleWorld.Domain → ω) {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (w : Multiplicative ω) (carrier : HandlerCarrier.State) (t : τ),
      (fun p : α × (Multiplicative ω × (HandlerCarrier.State × τ)) =>
          (p.1, (p.2.2.1, (p.2.2.2, p.2.1)))) <$>
        (simulateQ (WriterState.toStateful (impl.withAddCost cost)) computation).run
          (w, (carrier, t)) =
      (simulateQ (withExtra impl
        (fun queried x => x * Multiplicative.ofAdd (cost queried))) computation).run
        (carrier, (t, w)) := fun w carrier t =>
  run_reencode (WriterState.toStateful (impl.withAddCost cost)) impl
    (fun queried x => x * Multiplicative.ofAdd (cost queried))
    (fun p => (p.2.1, (p.2.2, p.1)))
    (fun queried st => by
      rw [WriterState.toStateful_run, WriterState.run_withAddCost_run, withExtra_run,
        map_eq_bind_pure_comp, bind_assoc, bind_assoc]
      exact congrArg (Bind.bind ((impl queried).run st.2))
        (funext fun step => by rw [pure_bind, pure_bind]; rfl))
    computation (w, (carrier, t))

/-! ## The step facts the wrapped handler needs

`Files` does not carry a step-level "served if the framing admitted it", because `queryStep`
bundles it. It is derivable from `queryStep` at `next := pure`, which is what this is: a query
followed by nothing is a step. -/

/-- **The served conjunct, at the step.** -/
theorem stepServedSelf
    {impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)}
    (hfiles : Files pk impl) (input : Bytes) (state : HandlerCarrier.State × τ)
    (step : OracleWorld.Range (Sum.inr input) × (HandlerCarrier.State × τ))
    (hstep : step ∈ support ((impl (Sum.inr input)).run state))
    (hadmits : FilesLeft pk state.1 input) : Served step.2.1 input := by
  have hrun : step ∈ support ((simulateQ impl
      ((query (spec := OracleWorld) (Sum.inr input) :
        OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) >>= pure)).run state) := by
    rw [simulateQ_bind,
      show simulateQ impl (query (spec := OracleWorld) (Sum.inr input) :
          OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) =
        (impl (Sum.inr input)) from by simp,
      StateT.run_bind, mem_support_bind_iff]
    exact ⟨step, hstep, by rw [simulateQ_pure, StateT.run_pure, support_pure]; rfl⟩
  obtain ⟨answer, mid, -, -, -, hserved, hrest⟩ := hfiles.queryStep input pure state step hrun
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  rw [show step.2 = mid from by rw [hrest]]
  exact hserved hadmits

/-! ## The interface transports -/

open scoped Classical in
/-- **A wrapped handler files if the handler underneath does**, whatever the extra component
is and however it is updated. The wrapper never touches the carrier, and the carrier is the only
thing `Files` looks at; every field below reads the step underneath and puts the carrier back. -/
theorem files_withExtra {ω : Type}
    {impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)}
    (hfiles : Files pk impl) (update : OracleWorld.Domain → ω → ω) :
    Files pk (withExtra impl update) where
  queryStep := by
    intro α input next state result hresult
    rw [simulateQ_bind,
      show simulateQ (withExtra impl update) (query (spec := OracleWorld) (Sum.inr input) :
          OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) =
        ((withExtra impl update) (Sum.inr input)) from by simp,
      StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    obtain ⟨inner, hinner, hvalue, hcarrier, -⟩ := withExtra_step impl update
      (Sum.inr input) state step
      hstep
    refine ⟨step.1, step.2, ?_, ?_, ?_, ?_, hrest⟩
    · rw [hcarrier, hvalue]
      exact hfiles.hashCached input (state.1, state.2.1) inner hinner
    · rw [hcarrier]
      exact hfiles.stepFraming (Sum.inr input) (state.1, state.2.1) inner hinner
    · rw [hcarrier]
      exact hfiles.stepGrows (Sum.inr input) (state.1, state.2.1) inner hinner
    · intro hadmits
      rw [hcarrier]
      exact stepServedSelf pk hfiles input (state.1, state.2.1) inner hinner hadmits
  runPersists := by
    intro α computation
    induction computation using OracleComp.inductionOn with
    | pure value =>
      intro state z hz
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [show z.2 = state from by rw [hz]]
      exact Grows.refl _
    | query_bind queried next ih =>
      intro state z hz
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hrest⟩ := hz
      obtain ⟨inner, hinner, -, hcarrier, -⟩ :=
        withExtra_step impl update queried state step hstep
      refine Grows.trans ?_ (ih step.1 step.2 z hrest)
      rw [hcarrier]
      exact hfiles.stepGrows queried (state.1, state.2.1) inner hinner
  invariant := by
    intro Inv hcache hfile α computation
    induction computation using OracleComp.inductionOn with
    | pure value =>
      intro state result hresult hinv
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [show result.2 = state from by rw [hresult]]
      exact hinv
    | query_bind queried next ih =>
      intro state result hresult hinv
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hrest⟩ := hresult
      obtain ⟨inner, hinner, -, hcarrier, -⟩ :=
        withExtra_step impl update queried state step hstep
      refine ih step.1 step.2 result hrest ?_
      rw [hcarrier]
      exact hfiles.invariant Inv hcache hfile
        (((query (spec := OracleWorld) queried :
          OracleComp OracleWorld (OracleWorld.Range queried)))) (state.1, state.2.1) inner
        (by rw [show simulateQ impl (query (spec := OracleWorld) queried :
              OracleComp OracleWorld (OracleWorld.Range queried)) = impl queried from by simp]
            exact hinner) hinv
  runFraming := by
    intro α computation
    induction computation using OracleComp.inductionOn with
    | pure value =>
      intro state z hz
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [show z.2 = state from by rw [hz]]
    | query_bind queried next ih =>
      intro state z hz
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hrest⟩ := hz
      obtain ⟨inner, hinner, -, hcarrier, -⟩ :=
        withExtra_step impl update queried state step hstep
      rw [ih step.1 step.2 z hrest, hcarrier]
      exact hfiles.stepFraming queried (state.1, state.2.1) inner hinner
  stepGrows := by
    intro queried state step hstep
    obtain ⟨inner, hinner, -, hcarrier, -⟩ :=
      withExtra_step impl update queried state step hstep
    rw [hcarrier]
    exact hfiles.stepGrows queried (state.1, state.2.1) inner hinner
  stepFraming := by
    intro queried state step hstep
    obtain ⟨inner, hinner, -, hcarrier, -⟩ :=
      withExtra_step impl update queried state step hstep
    rw [hcarrier]
    exact hfiles.stepFraming queried (state.1, state.2.1) inner hinner
  hashCached := by
    intro input state step hstep
    obtain ⟨inner, hinner, hvalue, hcarrier, -⟩ := withExtra_step impl update
      (Sum.inr input) state step
      hstep
    rw [hcarrier, hvalue]
    exact hfiles.hashCached input (state.1, state.2.1) inner hinner
  hashServed := by
    intro input state step hstep probe hserved
    obtain ⟨inner, hinner, -, hcarrier, -⟩ := withExtra_step impl update
      (Sum.inr input) state step hstep
    rw [hcarrier] at hserved
    exact hfiles.hashServed input (state.1, state.2.1) inner hinner probe hserved

open scoped Classical in
/-- **A counted handler files if the handler underneath does.** The counter is an extra
component updated per query, so this is `files_withExtra` and nothing more. -/
theorem files_withCount
    {impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp)}
    (hfiles : Files pk impl) : Files pk (withCount impl) :=
  files_withExtra pk hfiles fun queried count => count + hashCost queried

/-! ## And so does the projection law

`ServingForget.ForgetsAlong` is the other thing a bracketed phase asks of its handler. Counting
cannot disturb it, for the reason the counter was put where it was: the projection reads the
carrier and the counter is not in it.

**Stated at `withExtra`, not at the counter.** Nothing below reads the update, only that the
wrapper puts the step underneath back unchanged — so the counter's projection law is the
wrapper's, at `ω := Nat`. That matters because the counter is not the only extra the tail will
carry: a *split* counter is the same wrapper at `ω := Counts`, and it inherits these three
rather than repeating their inductions. -/

theorem withExtra_step_map {ω : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × ω)) :
    (fun z : OracleWorld.Range queried × (HandlerCarrier.State × (τ × ω)) =>
        (z.1, (z.2.1, z.2.2.1))) <$> ((withExtra impl update) queried).run state =
      (impl queried).run (state.1, state.2.1) := by
  rw [withExtra_run, map_eq_bind_pure_comp, bind_assoc]
  simp [Function.comp_def]

theorem run_withExtra_map {ω : Type} {α : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × ω),
      (fun z : α × (HandlerCarrier.State × (τ × ω)) => (z.1, (z.2.1, z.2.2.1))) <$>
          (simulateQ (withExtra impl update) computation).run state =
        (simulateQ impl computation).run (state.1, state.2.1) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, ← withExtra_step_map impl update queried state,
      bind_map_left]
    exact bind_congr fun step => ih step.1 step.2

/-- **A wrapped handler forgets wherever the handler underneath does**, whatever the extra
component is. -/
theorem forgetsAlong_withExtra {ω : Type} {S' : Type} (π : HandlerCarrier.State × τ → S')
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (update : OracleWorld.Domain → ω → ω)
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hforget : ServingForget.ForgetsAlong π impl outer') :
    ServingForget.ForgetsAlong (fun state : HandlerCarrier.State × (τ × ω) =>
      π (state.1, state.2.1)) (withExtra impl update) outer' := by
  intro β computation state
  rw [← hforget computation (state.1, state.2.1),
    ← run_withExtra_map impl update computation state, Functor.map_map]

theorem withCount_step_map
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerCarrier.State × (τ × Nat)) :
    (fun z : OracleWorld.Range queried × (HandlerCarrier.State × (τ × Nat)) =>
        (z.1, (z.2.1, z.2.2.1))) <$> ((withCount impl) queried).run state =
      (impl queried).run (state.1, state.2.1) :=
  withExtra_step_map impl (fun queried count => count + hashCost queried) queried state

theorem run_withCount_map {α : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Nat),
      (fun z : α × (HandlerCarrier.State × (τ × Nat)) => (z.1, (z.2.1, z.2.2.1))) <$>
          (simulateQ (withCount impl) computation).run state =
        (simulateQ impl computation).run (state.1, state.2.1) :=
  run_withExtra_map impl (fun queried count => count + hashCost queried) computation

/-- **A counted handler forgets wherever the handler underneath does.** -/
theorem forgetsAlong_withCount {S' : Type} (π : HandlerCarrier.State × τ → S')
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hforget : ServingForget.ForgetsAlong π impl outer') :
    ServingForget.ForgetsAlong (fun state : HandlerCarrier.State × (τ × Nat) =>
      π (state.1, state.2.1)) (withCount impl) outer' :=
  forgetsAlong_withExtra π impl (fun queried count => count + hashCost queried) outer' hforget

/-! ## The counter is `countAllHashes`

The tail reads its hash total from the handler's counter, because a bracketed game is not one
computation and there is nothing for `countAllHashes` to wrap. The count the rest of the
development is stated at is `countAllHashes`'s, so the two have to be the same number, and this
is where that is paid for: one induction, at any handler that forgets to the shared oracle.

The statement carries the counter the run *started* at, because a handler's counter accumulates
while `countAllHashes` begins at zero. That difference is the only one between them, and keeping
it explicit is what lets the three stages of a bracketed tail add up.
-/

theorem forgetsAlong_step {S' : Type} (π : HandlerCarrier.State × τ → S')
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (outer' : QueryImpl OracleWorld (StateT S' ProbComp))
    (hforget : ServingForget.ForgetsAlong π impl outer') (queried : OracleWorld.Domain)
    (state : HandlerCarrier.State × τ) :
    (fun z : OracleWorld.Range queried × (HandlerCarrier.State × τ) => (z.1, π z.2)) <$>
        (impl queried).run state = (outer' queried).run (π state) := by
  have hrun := hforget (liftM (OracleWorld.query queried) :
    OracleComp OracleWorld (OracleWorld.Range queried)) state
  rwa [show simulateQ impl (liftM (OracleWorld.query queried) :
      OracleComp OracleWorld (OracleWorld.Range queried)) = impl queried from by simp,
    show simulateQ outer' (liftM (OracleWorld.query queried) :
      OracleComp OracleWorld (OracleWorld.Range queried)) = outer' queried from by simp] at hrun

set_option maxHeartbeats 1000000 in
/-- **A counted handler's counter is `countAllHashes`'s count.** -/
theorem run_withCount_count {α : Type}
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (outer' : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (hforget : ServingForget.ForgetsAlong
      (fun state : HandlerCarrier.State × τ => state.1.cache) impl outer')
    (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Nat),
      (fun z : α × (HandlerCarrier.State × (τ × Nat)) => ((z.1, z.2.2.2), z.2.1.cache)) <$>
          (simulateQ (withCount impl) computation).run state =
        (fun r : (α × Nat) × QueryCache HashSpec => ((r.1.1, state.2.2 + r.1.2), r.2)) <$>
          (simulateQ outer' (countAllHashes computation)).run state.1.cache := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, GrowthBudget.countAllHashes_pure,
      simulateQ_pure, StateT.run_pure, map_pure, Nat.add_zero]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, withCount_run,
      bind_assoc, GrowthBudget.countAllHashes_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind,
      ← forgetsAlong_step (fun s : HandlerCarrier.State × τ => s.1.cache) impl outer' hforget
        queried (state.1, state.2.1), bind_map_left]
    refine bind_congr fun inner => ?_
    rw [pure_bind, ih inner.1 (inner.2.1, (inner.2.2, state.2.2 + hashCost queried)),
      simulateQ_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> (simulateQ outer' (countAllHashes (next inner.1))).run
      inner.2.1.cache) (funext fun result => ?_)
    show ((result.1.1, state.2.2 + hashCost queried + result.1.2), result.2) =
      ((result.1.1, state.2.2 + (hashCost queried + result.1.2)), result.2)
    rw [Nat.add_assoc]

/-! ## The shared oracle, counting

The tail's middle stage is a fused phase, and `ServingForget.run_fuseServing_map` projects it to
an unbracketed fused phase over whatever handler the outer one forgets to. For the tail that
projection has to keep the **count** as well as the cache, because the count is what the middle
stage contributes to the tail's value — so the handler on the far side is the shared oracle with
a counter beside it, and this is it.

It is a second counted handler rather than `withCount` again because the two states associate
differently: `ServedAgreement.Files` needs the carrier first, so the carrier's counted state is
`carrier × (recordings × count)`, while the shared oracle's is just `cache × count`. The
definitions are the same three lines and the proofs are the same two inductions; what cannot be
shared is the bracketing of the pair.

**It looks like duplication and the next reader will want to merge them, so: do not.** Merging
them means a reassociation lemma, and that lemma would have to be threaded through every call
site of both. *Duplication a reader can see beats an abstraction every call site has to pay
for* — six lines and two short inductions, against a rewrite in every use. -/

/-- The shared oracle with a hash counter beside its cache. -/
noncomputable def romWithCount :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Nat) ProbComp) :=
  fun queried state => do
    let step ← (KeygenUniform.rom queried).run state.1
    pure (step.1, (step.2, state.2 + hashCost queried))

theorem romWithCount_run (queried : OracleWorld.Domain) (state : QueryCache HashSpec × Nat) :
    (romWithCount queried).run state =
      (KeygenUniform.rom queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 + hashCost queried)) :
          ProbComp (OracleWorld.Range queried × (QueryCache HashSpec × Nat))) := rfl

theorem romWithCount_step_map (queried : OracleWorld.Domain)
    (state : QueryCache HashSpec × Nat) :
    (fun z : OracleWorld.Range queried × (QueryCache HashSpec × Nat) => (z.1, z.2.1)) <$>
        (romWithCount queried).run state = (KeygenUniform.rom queried).run state.1 := by
  rw [romWithCount_run, map_eq_bind_pure_comp, bind_assoc]
  simp [Function.comp_def]

set_option maxHeartbeats 1000000 in
/-- **Its counter is `countAllHashes`'s count.** The same statement as
`run_withCount_count`, at the other association, and carrying the counter the run started at for
the same reason: the tail's three stages add up only because each equation says what it started
from. -/
theorem run_romWithCount_count {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : QueryCache HashSpec × Nat,
      (fun z : α × (QueryCache HashSpec × Nat) => ((z.1, z.2.2), z.2.1)) <$>
          (simulateQ romWithCount computation).run state =
        (fun r : (α × Nat) × QueryCache HashSpec => ((r.1.1, state.2 + r.1.2), r.2)) <$>
          (simulateQ KeygenUniform.rom (countAllHashes computation)).run state.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, GrowthBudget.countAllHashes_pure,
      simulateQ_pure, StateT.run_pure, map_pure, Nat.add_zero]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, romWithCount_run,
      bind_assoc, GrowthBudget.countAllHashes_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind]
    refine bind_congr fun inner => ?_
    rw [pure_bind, ih inner.1 (inner.2, state.2 + hashCost queried), simulateQ_map,
      StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> (simulateQ KeygenUniform.rom
      (countAllHashes (next inner.1))).run inner.2) (funext fun result => ?_)
    show ((result.1.1, state.2 + hashCost queried + result.1.2), result.2) =
      ((result.1.1, state.2 + (hashCost queried + result.1.2)), result.2)
    rw [Nat.add_assoc]

end SlhDsaSecurity.CountedHandler

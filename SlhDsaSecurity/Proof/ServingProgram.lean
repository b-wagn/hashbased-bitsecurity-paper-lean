import SlhDsaSecurity.Proof.ServingCarrier

/-!
# The handler that files what the signer serves

`OpenCache.lazyProgram` now reads availability from a carrier, and `HandlerCarrier` has the
operations that change one. Nothing yet performs them. This file is the handler that does: the
same handler, with one addition — a query the framing recognises is **filed** in the same step
that caches its answer.

That the two happen together is the whole repair. `ServingCarrier.mem_disclosedAt_file_cacheAnswer`
says disclosure begins at the step that draws a digest; `disclosedAt_step` below is that
statement about this handler, which is where it has to be true. A design that filed when the
request completed would disclose *after* the signer's FORS reads, and the stalled run would read
a cell it must be blind to — the failure the whole notion exists to prevent.

**Nothing an adversary does files anything.** `HandlerCarrier.FilesLeft` is false whenever the
framing is clear, and only the signing oracle sets it; that is
`HandlerCarrier.not_filesLeft_of_clear`, and it is why this handler can be trusted where the
cache proxy could not.

**Filing is growth**, so the stalled stack is untouched: `servingProgram_persists` is
`CacheAvailability.lazyProgram_persists` for this handler, at the same `HandlerCarrier.Grows`,
and its consumers hand the relation straight into `hmono` without reading it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingProgram

open OpenCache LazyBudget CanonicalGraph

variable (publicSeed : Digest)

/-! ## What one query answers

`LazyBudget.lazyAnswer` is the answer, unchanged — this handler alters nothing about what is
*answered*. Two facts about it are needed, and neither is about the filing: the step grows the
carrier, and the step leaves its own input cached. -/

open scoped Classical in
/-- **A step of the answer grows the carrier.** -/
theorem lazyAnswer_grows (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (carrier : HandlerCarrier.State)
    (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    HandlerCarrier.Grows carrier step.2 := by
  classical
  rw [lazyAnswer] at hstep
  cases hcached : carrier.cache input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hstep
    rw [show step.2 = carrier from by rw [hstep]]
    exact HandlerCarrier.Grows.refl _
  | none =>
    rw [hcached] at hstep
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [hstep]]
      exact HandlerCarrier.grows_cacheAnswer carrier input answer hcached
    | none =>
      rw [hopen, support_map] at hstep
      obtain ⟨answer, -, heq⟩ := hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [← heq]]
      exact HandlerCarrier.grows_cacheAnswer carrier input answer hcached

/-- **A step of the answer leaves its own input cached**, holding the value it returned. This is
`QueryCached.step_cached` read through `LazyBudget.lazyAnswer_mem_randomOracle`: the handler's
replies are the shared oracle's, and the shared oracle caches what it answers. -/
theorem lazyAnswer_cached (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (carrier : HandlerCarrier.State)
    (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    step.2.cache input = some step.1 :=
  QueryCached.step_cached input carrier.cache (step.1, step.2.cache)
    (lazyAnswer_mem_randomOracle publicSeed availableAt table input carrier step hstep)

/-! ## The handler -/

open scoped Classical in
/-- **The handler.** `OpenCache.lazyProgram`, filing a query the framing recognises in the same
step that caches its answer. -/
noncomputable def servingProgram (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← lazyAnswer publicSeed availableAt table input state.1
        pure (step.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file step.2 input else step.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1))

open scoped Classical in
theorem servingProgram_run_inl (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (coin : unifSpec.Domain) (state : HandlerState) :
    ((servingProgram publicSeed pk availableAt table) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem servingProgram_run_inr (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState) :
    ((servingProgram publicSeed pk availableAt table) (Sum.inr input)).run state =
      lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
        (pure (step.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file step.2 input else step.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1)) : ProbComp _) := rfl

/-! ## What the stalled stack asks of it -/

open scoped Classical in
/-- **A step of the handler grows the carrier.** Filing adds a served input and the answer adds
a cache entry, and `HandlerCarrier.Grows` asks for no more than that — which is why the step the
notion exists for is growth like every other. -/
theorem servingProgram_persists (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table) queried).run
      state)) : HandlerCarrier.Grows state.1 step.2.1 := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
    exact HandlerCarrier.Grows.refl _
  · have hbind : step ∈ support
        (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
          (pure (inner.1,
            ((if HandlerCarrier.FilesLeft pk state.1 input then
                HandlerCarrier.file inner.2 input else inner.2),
              state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1 =
      (if HandlerCarrier.FilesLeft pk state.1 input then HandlerCarrier.file inner.2 input
        else inner.2) from by rw [hpure]]
    by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
    · rw [if_pos hfiles]
      exact HandlerCarrier.Grows.trans
        (lazyAnswer_grows publicSeed availableAt table input state.1 inner hinner)
        (HandlerCarrier.grows_file inner.2 input)
    · rw [if_neg hfiles]
      exact lazyAnswer_grows publicSeed availableAt table input state.1 inner hinner

/-! ## The ordering, at the handler that performs it -/

open scoped Classical in
/-- **A filed query's answer is disclosed from the step that drew it.** The filing and the
caching happen in one step, so there is no moment at which the signer has the digest and the
carrier does not — which is exactly what `RedrawCell.signInternal_congr`'s `hsigned` needs and
what the cache proxy was standing in for. -/
theorem disclosedAt_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState)
    (hfiles : HandlerCarrier.FilesLeft pk state.1 input)
    (step : HashOutput × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table)
      (Sum.inr input)).run state))
    (tree : Fin forsTrees) :
    GraphStakes.forsIndex (MessageDigest.forsIndices step.1) tree ∈
      ServingCarrier.disclosedAt step.2.1 (SplitCharged.forsKeyOfDigest step.1) := by
  classical
  have hbind : step ∈ support
      (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
        (pure (inner.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file inner.2 input else inner.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (HashOutput × HandlerState))) := hstep
  rw [mem_support_bind_iff] at hbind
  obtain ⟨inner, hinner, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hvalue : step.1 = inner.1 := by rw [hpure]
  have hstate : step.2.1 = HandlerCarrier.file inner.2 input := by
    rw [hpure]
    exact if_pos hfiles
  rw [hvalue, hstate]
  refine (ServedDisclosure.mem_servedAt HandlerCarrier.Served HandlerCarrier.cacheOf _ _ _).mpr
    ⟨input, inner.1, Multiset.mem_cons_self _ _, ?_, rfl, tree, rfl⟩
  exact lazyAnswer_cached publicSeed availableAt table input state.1 inner hinner


/-! ## The handler never writes the framing

It caches and it files, and neither changes what the state says is in flight. That is what makes
the framing a component only the signing oracle writes — and so what turns
`HandlerCarrier.not_filesLeft_of_clear` from a remark about the definition into a fact about the
run. -/

open scoped Classical in
/-- **The answer leaves the framing alone.** -/
theorem lazyAnswer_framing (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (carrier : HandlerCarrier.State)
    (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    step.2.framing = carrier.framing := by
  classical
  rw [lazyAnswer] at hstep
  cases hcached : carrier.cache input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hstep
    rw [show step.2 = carrier from by rw [hstep]]
  | none =>
    rw [hcached] at hstep
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [hstep]]
      exact HandlerCarrier.framing_cacheAnswer carrier input answer
    | none =>
      rw [hopen, support_map] at hstep
      obtain ⟨answer, -, heq⟩ := hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [← heq]]
      exact HandlerCarrier.framing_cacheAnswer carrier input answer

open scoped Classical in
/-- **The answer serves nothing.** Only the filing adds to the served set. -/
theorem lazyAnswer_served (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (carrier : HandlerCarrier.State)
    (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    step.2.served = carrier.served := by
  classical
  rw [lazyAnswer] at hstep
  cases hcached : carrier.cache input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hstep
    rw [show step.2 = carrier from by rw [hstep]]
  | none =>
    rw [hcached] at hstep
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [hstep]]
      exact HandlerCarrier.served_cacheAnswer carrier input answer
    | none =>
      rw [hopen, support_map] at hstep
      obtain ⟨answer, -, heq⟩ := hstep
      rw [show step.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [← heq]]
      exact HandlerCarrier.served_cacheAnswer carrier input answer

open scoped Classical in
/-- **A step of the handler leaves the framing alone.** -/
theorem servingProgram_framing (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table) queried).run
      state)) : step.2.1.framing = state.1.framing := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
  · have hbind : step ∈ support
        (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
          (pure (inner.1,
            ((if HandlerCarrier.FilesLeft pk state.1 input then
                HandlerCarrier.file inner.2 input else inner.2),
              state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    rw [show step.2.1 =
      (if HandlerCarrier.FilesLeft pk state.1 input then HandlerCarrier.file inner.2 input
        else inner.2) from by rw [hpure]]
    have hinnerFraming : inner.2.framing = state.1.framing :=
      lazyAnswer_framing publicSeed availableAt table input state.1 inner hinner
    by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
    · rw [if_pos hfiles, HandlerCarrier.framing_file]
      exact hinnerFraming
    · rw [if_neg hfiles]
      exact hinnerFraming

open scoped Classical in
/-- **A run of the handler leaves the framing alone**, which is what the bracket's invariant is
read against: the adversary's phase can run as long as it likes without the framing moving. -/
theorem servingProgram_run_framing (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        computation).run state) → z.2.1.framing = state.1.framing := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    rw [ih step.1 step.2 z hrest,
      servingProgram_framing publicSeed pk availableAt table queried state step hstep]


/-! ## What the served set contains

Every input the handler files is of the shape `HandlerCarrier.FilesLeft` demands — a message
input at the framing in flight — so a reachable carrier's served set is a set of message inputs.
That is the `hservedClass` hypothesis a recorder's disclosing test has to satisfy, and here it is
a consequence of the filing rule rather than something assumed about the test. -/

open scoped Classical in
/-- **A step files only message inputs.** -/
theorem served_isMessageInput_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (hstate : ∀ probe : Bytes, HandlerCarrier.Served state.1 probe →
      CombinedCharge.IsMessageInput pk probe)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table) queried).run
      state)) :
    ∀ probe : Bytes, HandlerCarrier.Served step.2.1 probe →
      CombinedCharge.IsMessageInput pk probe := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
    exact hstate
  · have hbind : step ∈ support
        (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
          (pure (inner.1,
            ((if HandlerCarrier.FilesLeft pk state.1 input then
                HandlerCarrier.file inner.2 input else inner.2),
              state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    have hinnerServed : ∀ probe : Bytes, HandlerCarrier.Served inner.2 probe →
        CombinedCharge.IsMessageInput pk probe := by
      intro probe hprobe
      have hserved : inner.2.served = state.1.served :=
        lazyAnswer_served publicSeed availableAt table input state.1 inner hinner
      refine hstate probe ?_
      show probe ∈ state.1.served
      rw [← hserved]
      exact hprobe
    rw [show step.2.1 =
      (if HandlerCarrier.FilesLeft pk state.1 input then HandlerCarrier.file inner.2 input
        else inner.2) from by rw [hpure]]
    by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
    · rw [if_pos hfiles]
      intro probe hprobe
      rcases Multiset.mem_cons.mp hprobe with heq | hrest
      · obtain ⟨framed, randomizer, -, hinput⟩ :=
          HandlerCarrier.framed_of_filesLeft pk state.1 input hfiles
        exact ⟨randomizer, framed, by rw [heq]; exact hinput⟩
      · exact hinnerServed probe hrest
    · rw [if_neg hfiles]
      exact hinnerServed

open scoped Classical in
/-- **A run files only message inputs.** -/
theorem served_isMessageInput_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState),
      (∀ probe : Bytes, HandlerCarrier.Served state.1 probe →
        CombinedCharge.IsMessageInput pk probe) →
      ∀ z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        computation).run state),
        ∀ probe : Bytes, HandlerCarrier.Served z.2.1 probe →
          CombinedCharge.IsMessageInput pk probe := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hstate z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hstate
  | query_bind queried next ih =>
    intro state hstate z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (served_isMessageInput_step publicSeed pk availableAt table queried state hstate step hstep)
      z hrest

end SlhDsaSecurity.ServingProgram

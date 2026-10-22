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



/-! ## What the run leaves served

`disclosedAt_step` says the handler discloses early enough. The opposite question is what it
discloses *at all*, and the answer has to be: only what the framing admitted. The composition
reads disclosure at the log, so a carrier that served an input no request ever asked for would
make positions available that the extraction's event does not — availability the charge has not
paid for.

The handler's two operations on the carrier are caching an answer and filing an input, and
nothing else touches it. So any property closed under those two survives a whole run, and the
one that matters is closed under them for a reason: caching changes nothing served, and filing
happens only where `HandlerCarrier.FilesLeft` holds. `servingProgram_invariant` is that
induction and `served_run` is the instance.

`served_run` takes the link to the framing as its one hypothesis — that an input `FilesLeft`
admits is an input the caller is willing to call served. That is deliberate and not a gap: the
handler files by a test on its own state, and what the framing *means* is the bracket's business,
not the handler's. `ServingPhase` is what supplies it. -/

open scoped Classical in
/-- **A step of the answer either leaves the carrier alone or caches one fresh entry.** The
shape `lazyAnswer_grows` and `lazyAnswer_framing` both read off, kept as a statement so that
anything else about the step can be read off it too. -/
theorem lazyAnswer_cases (availableAt : HandlerCarrier.State → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (carrier : HandlerCarrier.State)
    (step : HashOutput × HandlerCarrier.State)
    (hstep : step ∈ support (lazyAnswer publicSeed availableAt table input carrier)) :
    step.2 = carrier ∨ ∃ answer : HashOutput,
      step.2 = HandlerCarrier.cacheAnswer carrier input answer := by
  classical
  rw [lazyAnswer] at hstep
  cases hcached : carrier.cache input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hstep
    exact Or.inl (by rw [hstep])
  | none =>
    rw [hcached] at hstep
    cases hopen : openCache publicSeed (availableAt carrier) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hstep
      exact Or.inr ⟨answer, by rw [hstep]⟩
    | none =>
      rw [hopen, support_map] at hstep
      obtain ⟨answer, -, heq⟩ := hstep
      exact Or.inr ⟨answer, by rw [← heq]⟩

/-- **The filing test does not see the cache**, so an answer cannot change it. -/
theorem filesLeft_of_framing_eq (pk : PublicKey) {left right : HandlerCarrier.State}
    (hframing : right.framing = left.framing) (input : Bytes)
    (hfiles : HandlerCarrier.FilesLeft pk left input) :
    HandlerCarrier.FilesLeft pk right input := by
  obtain ⟨framed, hframed, randomizer, hinput⟩ := hfiles
  exact ⟨framed, hframing.trans hframed, randomizer, hinput⟩

open scoped Classical in
/-- **A property closed under the handler's two operations survives one step.** -/
theorem servingProgram_invariant_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (Inv : HandlerCarrier.State → Prop)
    (hcache : ∀ (carrier : HandlerCarrier.State) (input : Bytes) (answer : HashOutput),
      Inv carrier → Inv (HandlerCarrier.cacheAnswer carrier input answer))
    (hfile : ∀ (carrier : HandlerCarrier.State) (input : Bytes),
      Inv carrier → HandlerCarrier.FilesLeft pk carrier input →
        Inv (HandlerCarrier.file carrier input))
    (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table) queried).run
      state)) (hinv : Inv state.1) : Inv step.2.1 := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
    exact hinv
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
    have hinner' : Inv inner.2 := by
      rcases lazyAnswer_cases publicSeed availableAt table input state.1 inner hinner with
        hsame | ⟨answer, hcached⟩
      · rw [hsame]; exact hinv
      · rw [hcached]; exact hcache state.1 input answer hinv
    rw [show step.2.1 =
      (if HandlerCarrier.FilesLeft pk state.1 input then HandlerCarrier.file inner.2 input
        else inner.2) from by rw [hpure]]
    by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
    · rw [if_pos hfiles]
      exact hfile inner.2 input hinner'
        (filesLeft_of_framing_eq pk
          (lazyAnswer_framing publicSeed availableAt table input state.1 inner hinner) input
          hfiles)
    · rw [if_neg hfiles]
      exact hinner'

/-- **And therefore a whole run.** -/
theorem servingProgram_invariant {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (Inv : HandlerCarrier.State → Prop)
    (hcache : ∀ (carrier : HandlerCarrier.State) (input : Bytes) (answer : HashOutput),
      Inv carrier → Inv (HandlerCarrier.cacheAnswer carrier input answer))
    (hfile : ∀ (carrier : HandlerCarrier.State) (input : Bytes),
      Inv carrier → HandlerCarrier.FilesLeft pk carrier input →
        Inv (HandlerCarrier.file carrier input))
    (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (result : α × HandlerState),
      result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        computation).run state) → Inv state.1 → Inv result.2.1 := by
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
    exact ih step.1 step.2 result hrest
      (servingProgram_invariant_step publicSeed pk availableAt table Inv hcache hfile queried
        state step hstep hinv)

/-- **A run serves only inputs the framing admitted.** The one thing a caller supplies is that
an input `HandlerCarrier.FilesLeft` admits is an input it is willing to call served — which is
where the framing has to be tied to a request, and which is the bracket's business rather than
the handler's. -/
theorem served_run {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (admits : Bytes → Prop)
    (hadmits : ∀ (carrier : HandlerCarrier.State) (input : Bytes),
      HandlerCarrier.FilesLeft pk carrier input → admits input)
    (computation : OracleComp OracleWorld α) (state : HandlerState) (result : α × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run state))
    (hstart : ∀ input : Bytes, HandlerCarrier.Served state.1 input → admits input)
    (input : Bytes) (hserved : HandlerCarrier.Served result.2.1 input) : admits input := by
  refine servingProgram_invariant publicSeed pk availableAt table
    (fun carrier => ∀ probe : Bytes, HandlerCarrier.Served carrier probe → admits probe)
    (fun carrier probe answer hinv served hcached => hinv served hcached)
    (fun carrier probe hinv hfiles served hmem => ?_)
    computation state result hresult hstart input hserved
  rcases Multiset.mem_cons.mp hmem with rfl | hrest
  · exact hadmits carrier served hfiles
  · exact hinv served hrest

/-- **Nothing is served at the start of a run.** -/
theorem not_served_empty (input : Bytes) : ¬ HandlerCarrier.Served HandlerCarrier.empty input :=
  fun hserved => absurd hserved (by simp [HandlerCarrier.Served, HandlerCarrier.empty])

/-! ## One query, read as a step of a run

Both directions of the agreement between the carrier and the log are chains of single queries:
the signer asks its randomiser, then its digest, and what the carrier has to say about each is
the same four things. `servingProgram_query_step` is those four — the answer is cached, the
framing has not moved, the carrier has only grown, and if the framing admitted the input then it
is served — together with the continuation, so that a chain of queries is a chain of
applications of this one lemma.

Stating it with the continuation is what makes it chain. A lemma that spoke only about the state
after the first query would have to be re-proved for the second. -/

/-- **A run of the handler keeps every cache entry and everything served.** -/
theorem servingProgram_run_persists {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
        computation).run state) → HandlerCarrier.Grows state.1 z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact HandlerCarrier.Grows.refl _
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact HandlerCarrier.Grows.trans
      (servingProgram_persists publicSeed pk availableAt table queried state step hstep)
      (ih step.1 step.2 z hrest)

open scoped Classical in
/-- **What one hash query of a run leaves behind.** -/
theorem servingProgram_query_step {α : Type} (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (next : OracleWorld.Range (Sum.inr input) → OracleComp OracleWorld α)
    (state : HandlerState)
    (result : α × HandlerState)
    (hresult : result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      ((query (spec := OracleWorld) (Sum.inr input) :
          OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) >>= next)).run state)) :
    ∃ (answer : HashOutput) (mid : HandlerState),
      mid.1.cache input = some answer ∧ mid.1.framing = state.1.framing ∧
        HandlerCarrier.Grows state.1 mid.1 ∧
        (HandlerCarrier.FilesLeft pk state.1 input → HandlerCarrier.Served mid.1 input) ∧
        result ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
          (next answer)).run mid) := by
  classical
  rw [simulateQ_bind,
    show simulateQ (servingProgram publicSeed pk availableAt table)
        (query (spec := OracleWorld) (Sum.inr input) :
          OracleComp OracleWorld (OracleWorld.Range (Sum.inr input))) =
      (servingProgram publicSeed pk availableAt table) (Sum.inr input) from by simp,
    StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  refine ⟨step.1, step.2, ?_, ?_, ?_, ?_, hrest⟩
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
    have hvalue : step.1 = inner.1 := by rw [hpure]
    have hcache : step.2.1.cache = inner.2.cache := by
      rw [hpure]
      by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
      · rw [if_pos hfiles]; rfl
      · rw [if_neg hfiles]
    rw [hcache, hvalue]
    exact lazyAnswer_cached publicSeed availableAt table input state.1 inner hinner
  · exact servingProgram_framing publicSeed pk availableAt table _ state step hstep
  · exact servingProgram_persists publicSeed pk availableAt table _ state step hstep
  · intro hfiles
    have hbind : step ∈ support
        (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
          (pure (inner.1,
            ((if HandlerCarrier.FilesLeft pk state.1 input then
                HandlerCarrier.file inner.2 input else inner.2),
              state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, -, hpure⟩ := hbind
    rw [support_pure, Set.mem_singleton_iff] at hpure
    have hstate : step.2.1 = HandlerCarrier.file inner.2 input := by
      rw [hpure]
      exact if_pos hfiles
    rw [hstate]
    exact Multiset.mem_cons_self _ _


/-! ## The hash step on its own

`servingProgram_query_step` reads a step through the continuation that follows it, which is what
a chain of named queries wants. An induction over an arbitrary computation wants the same facts
about the step alone, with the continuation left to the induction hypothesis. These are those. -/

open scoped Classical in
/-- **A hash step leaves its own input cached**, holding the value it returned. -/
theorem servingProgram_hash_cached (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inr input) × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table)
      (Sum.inr input)).run state)) : step.2.1.cache input = some step.1 := by
  classical
  have hbind : step ∈ support
      (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
        (pure (inner.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file inner.2 input else inner.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
  rw [mem_support_bind_iff] at hbind
  obtain ⟨inner, hinner, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hvalue : step.1 = inner.1 := by rw [hpure]
  have hcache : step.2.1.cache = inner.2.cache := by
    rw [hpure]
    by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
    · rw [if_pos hfiles]; rfl
    · rw [if_neg hfiles]
  rw [hcache, hvalue]
  exact lazyAnswer_cached publicSeed availableAt table input state.1 inner hinner

open scoped Classical in
/-- **A hash step serves nothing but its own input.** Filing is the only thing that adds to the
served set, and a step files at most the input it is answering. -/
theorem servingProgram_hash_served (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inr input) × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk availableAt table)
      (Sum.inr input)).run state)) (probe : Bytes)
    (hserved : HandlerCarrier.Served step.2.1 probe) :
    HandlerCarrier.Served state.1 probe ∨ probe = input := by
  classical
  have hbind : step ∈ support
      (lazyAnswer publicSeed availableAt table input state.1 >>= fun inner =>
        (pure (inner.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file inner.2 input else inner.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
  rw [mem_support_bind_iff] at hbind
  obtain ⟨inner, hinner, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hinnerServed : inner.2.served = state.1.served :=
    lazyAnswer_served publicSeed availableAt table input state.1 inner hinner
  rw [show step.2.1 =
    (if HandlerCarrier.FilesLeft pk state.1 input then HandlerCarrier.file inner.2 input
      else inner.2) from by rw [hpure]] at hserved
  by_cases hfiles : HandlerCarrier.FilesLeft pk state.1 input
  · rw [if_pos hfiles] at hserved
    rcases Multiset.mem_cons.mp hserved with rfl | hrest
    · exact Or.inr rfl
    · exact Or.inl (by show probe ∈ state.1.served; rw [← hinnerServed]; exact hrest)
  · rw [if_neg hfiles] at hserved
    exact Or.inl (by show probe ∈ state.1.served; rw [← hinnerServed]; exact hserved)

/-! ## What the served set contains

Every input the handler files is of the shape `HandlerCarrier.FilesLeft` demands — a message
input at the framing in flight — so a reachable carrier's served set is a set of message inputs.
That is the `hservedClass` hypothesis a recorder's disclosing test has to satisfy, and here it is
a consequence of the filing rule rather than something assumed about the test.

Both are the general lemmas above at one predicate. They were written twice, once from each
side, before the general form existed; keeping the statements and dropping the second induction
is the whole of the merge. -/

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
      CombinedCharge.IsMessageInput pk probe :=
  servingProgram_invariant_step publicSeed pk availableAt table
    (fun carrier => ∀ probe : Bytes, HandlerCarrier.Served carrier probe →
      CombinedCharge.IsMessageInput pk probe)
    (fun _ _ _ hinv probe hprobe => hinv probe hprobe)
    (fun carrier input hinv hfiles probe hprobe => by
      rcases Multiset.mem_cons.mp hprobe with heq | hrest
      · obtain ⟨framed, randomizer, -, hinput⟩ :=
          HandlerCarrier.framed_of_filesLeft pk carrier input hfiles
        exact ⟨randomizer, framed, by rw [heq]; exact hinput⟩
      · exact hinv probe hrest)
    queried state step hstep hstate

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
          CombinedCharge.IsMessageInput pk probe :=
  fun state hstate z hz probe hprobe =>
    served_run publicSeed pk availableAt table (CombinedCharge.IsMessageInput pk)
      (fun carrier input hfiles => by
        obtain ⟨framed, randomizer, -, hinput⟩ :=
          HandlerCarrier.framed_of_filesLeft pk carrier input hfiles
        exact ⟨randomizer, framed, hinput⟩)
      computation state z hz hstate probe hprobe

end SlhDsaSecurity.ServingProgram

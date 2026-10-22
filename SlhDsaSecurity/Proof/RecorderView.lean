import SlhDsaSecurity.Proof.SplitPrefix
import SlhDsaSecurity.Proof.HandlerCarrier

/-!
# The recorder's state, as a parameter

`SplitPrefix.recorder` keeps two recordings beside a **cache**, and decides which recording an
answer joins by testing the input against that cache. That is exactly what the disclosing test
cannot be: an adversary that knows `SK.prf` makes any cache-readable "the signer served this"
test true with no request behind it, which is why `AnswerJoin.hdisclosing`'s right-to-left
direction is false. The test has to read the **carrier**, whose served set is written only by the
signing oracle.

So the state becomes a parameter. The recorder asks one thing of it and one thing only:

    cacheOf (update state input answer) = (cacheOf state).cacheQuery input answer

— enough to see whether a query is fresh and to install an answer, and nothing more, so that
every future instantiation pays for exactly this much. At `σ := QueryCache HashSpec` the two
fields are `id` and `cacheQuery` and `recorderOf_cache` says the generalised recorder **is**
`SplitPrefix.recorder`, so everything already proved about that one stands untouched. At
`σ := HandlerCarrier.State` they are `cacheOf` and `cacheAnswer`, and the disclosing test can be
the carrier's served set.

**The freshness rule and the served set stay different objects**, which is the thing to keep
checking. Freshness lives in `appendedOf`'s guard on `cacheOf state.1`, where it always was; the
served set lives in the carrier's own field. Instantiating the left test at the latter leaves the
former exactly where it is, so no instantiation can collapse the two even by accident.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecorderView

open SplitPrefix DigestTape

/-- What a recorder's state must provide, and the only law it must satisfy. -/
class CacheView (σ : Type) where
  /-- The cache the freshness test is read against. -/
  cacheOf : σ → QueryCache HashSpec
  /-- How an answer is installed. -/
  update : σ → Bytes → HashOutput → σ
  /-- Installing an answer caches it, and says nothing else. -/
  cache_update : ∀ (state : σ) (input : Bytes) (answer : HashOutput),
    cacheOf (update state input answer) = (cacheOf state).cacheQuery input answer

/-- The cache is its own view. -/
instance : CacheView (QueryCache HashSpec) where
  cacheOf := id
  update := fun cache input answer => cache.cacheQuery input answer
  cache_update := fun _ _ _ => rfl

/-- And so is the handler's carrier, at the operations it already has. -/
instance : CacheView HandlerCarrier.State where
  cacheOf := HandlerCarrier.cacheOf
  update := HandlerCarrier.cacheAnswer
  cache_update := fun _ _ _ => rfl

variable {σ : Type} [CacheView σ]

/-- The state at a general view: the carrier and the two recordings. -/
abbrev StateOf (σ : Type) := σ × Record × Record

open scoped Classical in
/-- What the two recordings become when a query is answered. The guard is freshness, read at
the view's cache, exactly as `SplitPrefix.appended` reads it at the cache itself. -/
noncomputable def appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) : Record × Record :=
  if CacheView.cacheOf state.1 input = none ∧ leftKeep input state.1 then
    (state.2.1 ++ [(input, answer)], state.2.2)
  else if CacheView.cacheOf state.1 input = none ∧ rightKeep input state.1 then
    (state.2.1, state.2.2 ++ [(input, answer)])
  else state.2

theorem left_prefix_appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) :
    state.2.1 <+: (appendedOf leftKeep rightKeep input state answer).1 := by
  classical
  rw [appendedOf]
  split
  · exact List.prefix_append _ _
  · split
    · exact List.prefix_rfl
    · exact List.prefix_rfl

theorem right_prefix_appendedOf (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) :
    state.2.2 <+: (appendedOf leftKeep rightKeep input state answer).2 := by
  classical
  rw [appendedOf]
  split
  · exact List.prefix_rfl
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_rfl

/-! ### Reading the two tests -/

open scoped Classical in
theorem appendedOf_of_cached (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer cached : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some cached) :
    appendedOf leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appendedOf, if_neg (by rw [hcached]; simp), if_neg (by rw [hcached]; simp)]

open scoped Classical in
theorem appendedOf_of_left (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state.1 input = none) (hleft : leftKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer =
      (state.2.1 ++ [(input, answer)], state.2.2) := by
  classical
  rw [appendedOf, if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem appendedOf_of_right (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state.1 input = none) (hleft : ¬ leftKeep input state.1)
    (hright : rightKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer =
      (state.2.1, state.2.2 ++ [(input, answer)]) := by
  classical
  rw [appendedOf, if_neg (fun hboth => hleft hboth.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem appendedOf_of_neither (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (answer : HashOutput) (hleft : ¬ leftKeep input state.1)
    (hright : ¬ rightKeep input state.1) :
    appendedOf leftKeep rightKeep input state answer = state.2 := by
  classical
  rw [appendedOf, if_neg (fun hboth => hleft hboth.2), if_neg (fun hboth => hright hboth.2)]

open scoped Classical in
/-- **The recorder at a general view.** The two branches are the shared oracle's own — a hit
returns the cached answer and leaves the state, a miss draws and installs — so at the cache this
is `SplitPrefix.recorder` and not merely something with its law. -/
noncomputable def recorderOf (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (StateOf σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        match CacheView.cacheOf state.1 input with
        | some cached =>
            (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
              ProbComp _)
        | none =>
            (fun answer => (answer,
              (CacheView.update state.1 input answer,
                appendedOf leftKeep rightKeep input state answer))) <$>
              ($ᵗ HashOutput : ProbComp _)

open scoped Classical in
theorem recorderOf_run_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : StateOf σ) :
    ((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem recorderOf_run_inr_some (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (cached : HashOutput)
    (hcached : CacheView.cacheOf state.1 input = some cached) :
    ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  show (match CacheView.cacheOf state.1 input with
    | some cached => (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp _)
    | none => _) = _
  rw [hcached]
  rfl

open scoped Classical in
theorem recorderOf_run_inr_none (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (hfresh : CacheView.cacheOf state.1 input = none) :
    ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      (((fun answer => (answer,
        (CacheView.update state.1 input answer,
          appendedOf leftKeep rightKeep input state answer))) <$>
        ($ᵗ HashOutput : ProbComp _)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × StateOf σ)) := by
  classical
  show (match CacheView.cacheOf state.1 input with
    | some cached => (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp _)
    | none => _) = _
  rw [hfresh]

/-! ## At the cache, it is the recorder `SplitPrefix` already has

So nothing proved there has to move, and the generalisation is a widening rather than a
replacement. -/

open scoped Classical in
theorem appendedOf_cache (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitState) (answer : HashOutput) :
    appendedOf leftKeep rightKeep input state answer =
      appended leftKeep rightKeep input state answer := rfl

open scoped Classical in
/-- **The generalised recorder at the cache is `SplitPrefix.recorder`.** -/
theorem recorderOf_cache (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) :
    recorderOf leftKeep rightKeep = recorder leftKeep rightKeep := by
  classical
  funext queried state
  rcases queried with coin | input
  · rfl
  · show ((recorderOf leftKeep rightKeep) (Sum.inr input)).run state =
      ((recorder leftKeep rightKeep) (Sum.inr input)).run state
    rw [SplitPrefix.recorder_run_inr]
    cases hcached : state.1 input with
    | some cached =>
      rw [recorderOf_run_inr_some leftKeep rightKeep input state cached hcached,
        QueryImpl.withCaching_run_some _ hcached, pure_bind]
      rfl
    | none =>
      rw [recorderOf_run_inr_none leftKeep rightKeep input state hcached,
        QueryImpl.withCaching_run_none _ hcached]
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_def]
      rfl

/-! ## What the law buys

The law is read in exactly two ways, and every proof below goes through those two readings
rather than through `CacheView.update` itself. That is the point of keeping the law single: a
second one would have to be paid for here and again at every instantiation. -/

theorem cacheOf_update_self (state : σ) (input : Bytes) (answer : HashOutput) :
    CacheView.cacheOf (CacheView.update state input answer) input = some answer := by
  rw [CacheView.cache_update, QueryCache.cacheQuery_self]

theorem cacheOf_update_of_ne (state : σ) (input probe : Bytes) (answer : HashOutput)
    (hne : probe ≠ input) :
    CacheView.cacheOf (CacheView.update state input answer) probe =
      CacheView.cacheOf state probe := by
  rw [CacheView.cache_update, QueryCache.cacheQuery_of_ne _ _ hne]

/-! ## One step, read four ways

Below this point nothing mentions `CacheView.update` again. A hash query does one of two things
to the state, and these four lemmas are everything the inductions need to know about which. -/

open scoped Classical in
/-- **A private sample leaves the state alone.** -/
theorem recorderOf_step_inl (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inl coin) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [recorderOf_run_inl, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

open scoped Classical in
/-- **The two shapes a hash query's step can have.** Either the input was cached, and the state
is untouched; or it was fresh, and the answer is installed. Either way the recordings take that
answer's appending. Because `recorderOf` is written as the shared oracle's own two cases, this
is the whole of a step, and the three readings that follow are its consequences. -/
theorem recorderOf_step (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    (CacheView.cacheOf state.1 input = some step.1 ∧
        step.2 = (state.1, appendedOf leftKeep rightKeep input state step.1)) ∨
      (CacheView.cacheOf state.1 input = none ∧
        step.2 = (CacheView.update state.1 input step.1,
          appendedOf leftKeep rightKeep input state step.1)) := by
  classical
  cases hcached : CacheView.cacheOf state.1 input with
  | some cached =>
    rw [recorderOf_run_inr_some leftKeep rightKeep input state cached hcached, support_pure,
      Set.mem_singleton_iff] at hstep
    subst hstep
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    rw [recorderOf_run_inr_none leftKeep rightKeep input state hcached, support_map] at hstep
    obtain ⟨answer, -, hpair⟩ := hstep
    subst hpair
    exact Or.inr ⟨rfl, rfl⟩

open scoped Classical in
/-- **A step appends exactly what `appendedOf` says.** -/
theorem recorderOf_step_record (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    step.2.2 = appendedOf leftKeep rightKeep input state step.1 := by
  rcases recorderOf_step leftKeep rightKeep input state step hstep with ⟨-, hshape⟩ | ⟨-, hshape⟩ <;>
    rw [hshape]

open scoped Classical in
/-- **After its own query the answer is in the cache**, whichever branch the step took: a hit
reads the entry that was already there, a miss installs one. -/
theorem recorderOf_step_cache_self (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state)) :
    CacheView.cacheOf step.2.1 input = some step.1 := by
  rcases recorderOf_step leftKeep rightKeep input state step hstep with
    ⟨hcached, hshape⟩ | ⟨-, hshape⟩
  · rw [show step.2.1 = state.1 from by rw [hshape]]
    exact hcached
  · rw [show step.2.1 = CacheView.update state.1 input step.1 from by rw [hshape]]
    exact cacheOf_update_self state.1 input step.1

open scoped Classical in
/-- **A step never loses an entry.** -/
theorem recorderOf_step_persists (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (state : StateOf σ) (step : OracleWorld.Range (Sum.inr input) × StateOf σ)
    (hstep : step ∈ support (((recorderOf leftKeep rightKeep) (Sum.inr input)).run state))
    (probe : Bytes) (value : HashOutput) (hentry : CacheView.cacheOf state.1 probe = some value) :
    CacheView.cacheOf step.2.1 probe = some value := by
  classical
  rcases recorderOf_step leftKeep rightKeep input state step hstep with
    ⟨-, hshape⟩ | ⟨hfresh, hshape⟩
  · rw [show step.2.1 = state.1 from by rw [hshape]]
    exact hentry
  · rw [show step.2.1 = CacheView.update state.1 input step.1 from by rw [hshape]]
    have hne : probe ≠ input := by
      intro hsame
      rw [hsame, hfresh] at hentry
      simp at hentry
    rw [cacheOf_update_of_ne state.1 input probe step.1 hne]
    exact hentry

/-! ## The three facts about a whole run

These are `SplitPrefix.record_prefix`, `recorder_cache_value_persists`, `mem_record_of_cache`
and `left_record_keep_final` with the cache replaced by the view. The parametric half of the
join reaches only the last two of them; the rest of `SplitPrefix` stays where it is, about the
same object by `recorderOf_cache`. -/

open scoped Classical in
/-- **Both recordings only grow.** -/
theorem recordOf_prefix {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state)) :
    state.2.1 <+: result.2.2.1 ∧ state.2.2 <+: result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨hleft, hright⟩ := ih step.1 step.2 result hrest
    have hstepPrefix : state.2.1 <+: step.2.2.1 ∧ state.2.2 <+: step.2.2.2 := by
      rcases queried with coin | input
      · rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
        exact ⟨List.prefix_rfl, List.prefix_rfl⟩
      · rw [recorderOf_step_record leftKeep rightKeep input state step hstep]
        exact ⟨left_prefix_appendedOf leftKeep rightKeep input state step.1,
          right_prefix_appendedOf leftKeep rightKeep input state step.1⟩
    exact ⟨hstepPrefix.1.trans hleft, hstepPrefix.2.trans hright⟩

open scoped Classical in
/-- **An entry of the view's cache survives the run.** -/
theorem recorderOf_cache_value_persists {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state))
    (input : Bytes) (answer : HashOutput)
    (hentry : CacheView.cacheOf state.1 input = some answer) :
    CacheView.cacheOf result.2.1 input = some answer := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | probe
    · rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
      exact hentry
    · exact recorderOf_step_persists leftKeep rightKeep probe state step hstep input answer hentry

open scoped Classical in
/-- **Every class answer the run installed was recorded**, on one side or the other. The two
tests cover the class between them, and which side takes the entry is decided by the view in
force at the time. -/
theorem mem_recordOf_of_cache {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop)
    (hcover : ∀ (input : Bytes) (view : σ), inClass input →
      leftKeep input view ∨ rightKeep input view)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state))
    (input : Bytes) (answer : HashOutput) (hclass : inClass input)
    (hfresh : CacheView.cacheOf state.1 input = none)
    (hfinal : CacheView.cacheOf result.2.1 input = some answer) :
    (input, answer) ∈ result.2.2.1 ∨ (input, answer) ∈ result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at hfinal
    rw [hfresh] at hfinal
    simp at hfinal
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases queried with coin | probe
    · refine ih step.1 step.2 result hrest ?_ hfinal
      rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
      exact hfresh
    · by_cases hsame : input = probe
      · subst hsame
        have hpersist : CacheView.cacheOf result.2.1 input = some step.1 :=
          recorderOf_cache_value_persists leftKeep rightKeep (next step.1) step.2 result hrest
            input step.1 (recorderOf_step_cache_self leftKeep rightKeep input state step hstep)
        have hvalue : step.1 = answer := by
          rw [hpersist] at hfinal
          exact Option.some.inj hfinal
        obtain ⟨hgrowLeft, hgrowRight⟩ :=
          recordOf_prefix leftKeep rightKeep (next step.1) step.2 result hrest
        have hrecStep := recorderOf_step_record leftKeep rightKeep input state step hstep
        by_cases hleft : leftKeep input state.1
        · refine Or.inl (hgrowLeft.subset ?_)
          rw [hrecStep, appendedOf_of_left leftKeep rightKeep input state step.1 hfresh hleft,
            hvalue]
          simp
        · have hright : rightKeep input state.1 := by
            rcases hcover input state.1 hclass with hcase | hcase
            · exact absurd hcase hleft
            · exact hcase
          refine Or.inr (hgrowRight.subset ?_)
          rw [hrecStep,
            appendedOf_of_right leftKeep rightKeep input state step.1 hfresh hleft hright,
            hvalue]
          simp
      · refine ih step.1 step.2 result hrest ?_ hfinal
        rcases recorderOf_step leftKeep rightKeep probe state step hstep with
          ⟨-, hshape⟩ | ⟨-, hshape⟩
        · rw [show step.2.1 = state.1 from by rw [hshape]]
          exact hfresh
        · rw [show step.2.1 = CacheView.update state.1 probe step.1 from by rw [hshape],
            cacheOf_update_of_ne state.1 probe input step.1 hsame]
          exact hfresh

/-- **Installing a fresh answer loses no entry.** -/
theorem persists_update (state : σ) (probe : Bytes) (answer : HashOutput)
    (hfresh : CacheView.cacheOf state probe = none) (input : Bytes) (value : HashOutput)
    (hentry : CacheView.cacheOf state input = some value) :
    CacheView.cacheOf (CacheView.update state probe answer) input = some value := by
  have hne : input ≠ probe := by
    intro hsame
    rw [hsame, hfresh] at hentry
    simp at hentry
  rw [cacheOf_update_of_ne state probe input answer hne]
  exact hentry

/-! ## What the disclosing recording's entries satisfy at the end

**The filing test and the disclosure it records are two predicates, not one.** A test that is
read at the state a query is made from can be a flag the signing oracle holds up while it
serves — which is the only kind of disclosing test an adversary cannot forge, since a
cache-readable one it can make true by holding `SK.prf`. Such a flag is *false again* by the
end of the run, so it cannot also be the predicate the entries satisfy at the end.

So `endKeep` is separate, and the two are joined by what a step does: filing an answer puts the
input into whatever the end predicate reads, and no later step takes it out. At a cache-readable
test the two collapse — `left_recordOf_keep_final` below is this lemma with `endKeep := leftKeep`
and both laws read off the old monotonicity — so nothing that used the collapsed form moves. -/

open scoped Classical in
/-- **Every entry of the disclosing recording satisfies the end predicate at the end of the
run.** -/
theorem left_recordOf_endKeep_final {α : Type} (leftKeep rightKeep endKeep : Bytes → σ → Prop)
    (hfile : ∀ (input : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view input = none → leftKeep input view →
        endKeep input (CacheView.update view input answer))
    (hkeeps : ∀ (input probe : Bytes) (view : σ) (answer : HashOutput),
      CacheView.cacheOf view probe = none → endKeep input view →
        endKeep input (CacheView.update view probe answer))
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.1, endKeep entry.1 state.1) :
    ∀ entry ∈ result.2.2.1, endKeep entry.1 result.2.1 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem] at *
    exact hstart
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | input
    · rw [recorderOf_step_inl leftKeep rightKeep coin state step hstep]
      exact hstart
    · have hrecStep := recorderOf_step_record leftKeep rightKeep input state step hstep
      cases hcached : CacheView.cacheOf state.1 input with
      | some cached =>
        rcases recorderOf_step leftKeep rightKeep input state step hstep with
          ⟨-, hshape⟩ | ⟨hbad, -⟩
        · rw [show step.2.1 = state.1 from by rw [hshape],
            show step.2.2 = state.2 from by
              rw [hshape,
                appendedOf_of_cached leftKeep rightKeep input state step.1 cached hcached]]
          exact hstart
        · rw [hcached] at hbad
          simp at hbad
      | none =>
        have hinstalled : step.2.1 = CacheView.update state.1 input step.1 := by
          rcases recorderOf_step leftKeep rightKeep input state step hstep with
            ⟨hbad, -⟩ | ⟨-, hshape⟩
          · rw [hcached] at hbad
            simp at hbad
          · rw [hshape]
        have hcarry : ∀ entry ∈ state.2.1, endKeep entry.1 step.2.1 := by
          intro entry hentry
          rw [hinstalled]
          exact hkeeps entry.1 input state.1 step.1 hcached (hstart entry hentry)
        by_cases hleft : leftKeep input state.1
        · rw [hrecStep, appendedOf_of_left leftKeep rightKeep input state step.1 hcached hleft]
          intro entry hentry
          rcases List.mem_append.mp hentry with hold | hnew
          · exact hcarry entry hold
          · rw [List.mem_singleton.mp hnew, hinstalled]
            exact hfile input state.1 step.1 hcached hleft
        · by_cases hright : rightKeep input state.1
          · rw [hrecStep,
              appendedOf_of_right leftKeep rightKeep input state step.1 hcached hleft hright]
            exact hcarry
          · rw [hrecStep,
              appendedOf_of_neither leftKeep rightKeep input state step.1 hleft hright]
            exact hcarry

open scoped Classical in
/-- **Every entry of the disclosing recording still passes its own test at the end of the run**,
when that test is monotone in the view's cache. The collapsed case: one predicate in both roles,
which is what a cache-readable disclosing test allows and a flag does not. -/
theorem left_recordOf_keep_final {α : Type} (leftKeep rightKeep : Bytes → σ → Prop)
    (hmono : ∀ (input : Bytes) (view later : σ),
      (∀ (probe : Bytes) (value : HashOutput),
        CacheView.cacheOf view probe = some value →
          CacheView.cacheOf later probe = some value) →
        leftKeep input view → leftKeep input later)
    (computation : OracleComp OracleWorld α) (state : StateOf σ) (result : α × StateOf σ)
    (hmem : result ∈ support ((simulateQ (recorderOf leftKeep rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.1, leftKeep entry.1 state.1) :
    ∀ entry ∈ result.2.2.1, leftKeep entry.1 result.2.1 :=
  left_recordOf_endKeep_final leftKeep rightKeep leftKeep
    (fun input view answer hfresh hkeep =>
      hmono input view (CacheView.update view input answer)
        (persists_update view input answer hfresh) hkeep)
    (fun input probe view answer hfresh hkeep =>
      hmono input view (CacheView.update view probe answer)
        (persists_update view probe answer hfresh) hkeep)
    computation state result hmem hstart

end SlhDsaSecurity.RecorderView

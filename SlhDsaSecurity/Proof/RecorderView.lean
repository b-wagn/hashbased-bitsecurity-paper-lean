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
      (fun answer => (answer,
        (CacheView.update state.1 input answer,
          appendedOf leftKeep rightKeep input state answer))) <$>
        ($ᵗ HashOutput : ProbComp _) := by
  classical
  show (match CacheView.cacheOf state.1 input with
    | some cached => (pure (cached, (state.1, appendedOf leftKeep rightKeep input state cached)) :
        ProbComp _)
    | none => _) = _
  rw [hfresh]
  rfl

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

end SlhDsaSecurity.RecorderView

import SlhDsaSecurity.Proof.CountedHandler

/-!
# The filing handler is a counted one

`ServingProgram.servingProgram` carries a counter and advances it by one at each hash call,
written inline in its own step rather than by wrapping a handler that does not count. Nothing
needed otherwise until the budget did: `CountedHandler.run_withCount_count` identifies
`withCount`'s counter with `countAllHashes`'s total, and that is the only route from a handler's
own counter to the number `HasTotalBudget` caps.

So the handler is exhibited here as a counted one. `servingUncounted` is itself with the counter
taken away, and `withCount_servingUncounted` puts it back. The two sides agree because
`hashCost` is one per hash call and nothing per uniform sample — the same arithmetic that makes
`ProbeContainment.length_appended_eq_hashCost` hold, read at the counter instead of at the probe
list.

**What this buys is not only the count.** `files_withCount`, `forgetsAlong_withCount` and
`run_withCount_map` are all stated at `withCount impl`, so each of them now applies to the
filing handler without being restated for it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingCounted

open Security CanonicalGraph OpenCache ServingProgram CountedHandler

open scoped Classical in
/-- **`ServingProgram.servingProgram` with its counter taken away.** -/
noncomputable def servingUncounted (publicSeed : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) :
    QueryImpl OracleWorld
      (StateT (HandlerCarrier.State × List (Bytes × HandlerCarrier.State)) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← LazyBudget.lazyAnswer publicSeed availableAt table input state.1
        pure (step.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file step.2 input else step.2),
            state.2 ++ [(input, state.1)]))

open scoped Classical in
/-- **And putting the counter back is `withCount`.** -/
theorem withCount_servingUncounted (publicSeed : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding) :
    withCount (servingUncounted publicSeed pk availableAt table) =
      servingProgram publicSeed pk availableAt table := by
  classical
  funext queried state
  show ((withCount (servingUncounted publicSeed pk availableAt table)) queried).run state =
    ((servingProgram publicSeed pk availableAt table) queried).run state
  rcases queried with coin | input
  · rw [withCount_run, servingProgram_run_inl]
    show (do
      let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
      pure (value, (state.1, state.2.1))) >>= _ = _
    rw [bind_assoc]
    refine bind_congr fun value => ?_
    rw [pure_bind, show hashCost (Sum.inl coin) = 0 from rfl, Nat.add_zero]
  · rw [withCount_run, servingProgram_run_inr]
    show (LazyBudget.lazyAnswer publicSeed availableAt table input state.1 >>= fun step =>
      (pure (step.1,
        ((if HandlerCarrier.FilesLeft pk state.1 input then
            HandlerCarrier.file step.2 input else step.2),
          state.2.1 ++ [(input, state.1)])) : ProbComp _)) >>= _ = _
    rw [bind_assoc]
    refine bind_congr fun step => ?_
    rw [pure_bind, show hashCost (Sum.inr input) = 1 from rfl]
    rfl

end SlhDsaSecurity.ServingCounted

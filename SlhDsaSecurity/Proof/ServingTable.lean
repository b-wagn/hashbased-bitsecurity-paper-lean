import SlhDsaSecurity.Proof.HonestTail
import SlhDsaSecurity.Proof.HandlerLenient

/-!
# The game's run, answered by the handler that files

`RedrawCell.probEvent_rom_eq_lazy` identifies the game's run with `OpenCache.lazyProgram` at
total availability, started from nothing. The charge now has to read a handler that **files**,
because the availability it is stated at is the served one and only the serving handler keeps a
served set for it to be read from. So the same identification is made here for
`ServingProgram.servingProgram`.

**A transport from the lazy statement will not do, and the reason is the point of the exercise.**
The two handlers answer alike — at total availability `lazyAnswer` reads the carrier only
through its cache, and filing leaves the cache alone — so the values and the caches agree. But
the record's entries carry the *whole* carrier at the moment of the probe, served set included,
and that is exactly what the charge reads when it asks whether a probe was sensitive. The two
runs therefore differ in precisely the data the charge needs, and the identification has to be
proved at the handler the charge will read.

What makes the proof a mirror rather than a new argument is that the filing never touches the
cache: `HandlerCarrier.cache_file`. Every cache-level step is the lazy one, and the `if` the
filing introduces disappears under `cache_fileIf` before any of it is reached.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.ServingTable

open Security CanonicalGraph OpenCache ServingProgram

/-! ## Filing leaves the cache alone -/

open scoped Classical in
/-- **A filed carrier has the cache it had.** The test is read at the state the query was made
from and the filing is applied to the answered carrier, so the two are different states; what
matters is only that neither branch writes the cache. -/
theorem cache_fileIf (pk : PublicKey) (carrier filed : HandlerCarrier.State) (input : Bytes) :
    (if HandlerCarrier.FilesLeft pk carrier input then HandlerCarrier.file filed input
      else filed).cache = filed.cache := by
  classical
  split <;> simp

open scoped Classical in
/-- The serving handler's hash step, with the answer's cases exposed. -/
theorem servingProgram_run_inr_cases (publicSeed : Digest) (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState) :
    ((servingProgram publicSeed pk availableAt table) (Sum.inr input)).run state =
      (match state.1.cache input with
        | some cached => (pure (cached, state.1) : ProbComp _)
        | none =>
          match openCache publicSeed (availableAt state.1) table input with
          | some answer => pure (answer, HandlerCarrier.cacheAnswer state.1 input answer)
          | none =>
            (fun answer => (answer, HandlerCarrier.cacheAnswer state.1 input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun step =>
        (pure (step.1,
          ((if HandlerCarrier.FilesLeft pk state.1 input then
              HandlerCarrier.file step.2 input else step.2),
            state.2.1 ++ [(input, state.1)], state.2.2 + 1)) : ProbComp _) := rfl

/-! ## The step, and the invariant it preserves -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The game's step is the serving handler's step, read through the union.** -/
theorem rom_union_step (publicSeed : Digest) (pk : PublicKey) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (carrier : HandlerCarrier.State)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (hcompat : RedrawCell.Compatible publicSeed table carrier.cache) :
    (KeygenUniform.rom queried).run (RedrawCell.unionCache publicSeed table carrier.cache) =
      (fun z : OracleWorld.Range queried × HandlerState =>
          (z.1, RedrawCell.unionCache publicSeed table z.2.1.cache)) <$>
        ((servingProgram publicSeed pk (fun _ _ => True) table) queried).run
          (carrier, record, count) := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, DigestTape.rom_run_inl]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · rw [servingProgram_run_inr_cases, DigestTape.rom_run_inr]
    cases hcached : carrier.cache input with
    | some cached =>
      rw [QueryImpl.withCaching_run_some _ (hcompat input cached hcached)]
      simp only [pure_bind, map_pure, cache_fileIf]
    | none =>
      cases hopen : openCache publicSeed (fun _ => True) table input with
      | some answer =>
        rw [QueryImpl.withCaching_run_some _
          (RedrawCell.unionCache_of_open publicSeed table carrier.cache input answer hopen)]
        simp only [pure_bind, map_pure, cache_fileIf, HandlerCarrier.cacheAnswer,
          RedrawCell.unionCache_cacheQuery_open publicSeed table carrier.cache input answer hopen]
      | none =>
        rw [QueryImpl.withCaching_run_none _
          (by rw [RedrawCell.unionCache_of_none publicSeed table carrier.cache input hopen,
            hcached])]
        simp only [uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply, pure_bind, cache_fileIf, HandlerCarrier.cacheAnswer,
          RedrawCell.unionCache_cacheQuery_fresh publicSeed table carrier.cache input hopen]
        rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The serving handler's cache stays compatible with the table.** -/
theorem compatible_step (publicSeed : Digest) (pk : PublicKey) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (carrier : HandlerCarrier.State)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (hcompat : RedrawCell.Compatible publicSeed table carrier.cache)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((servingProgram publicSeed pk (fun _ _ => True) table)
      queried).run (carrier, record, count))) :
    RedrawCell.Compatible publicSeed table step.2.1.cache := by
  classical
  rcases queried with coin | input
  · rw [servingProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1 = carrier from by rw [hpure]]
    exact hcompat
  · have hbind : step ∈ support
        (LazyBudget.lazyAnswer publicSeed (fun _ _ => True) table input carrier >>= fun inner =>
          (pure (inner.1,
            ((if HandlerCarrier.FilesLeft pk carrier input then
                HandlerCarrier.file inner.2 input else inner.2),
              record ++ [(input, carrier)], count + 1)) :
            ProbComp (OracleWorld.Range (Sum.inr input) × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1.cache = inner.2.cache from by
      rw [show step.2.1 = (if HandlerCarrier.FilesLeft pk carrier input then
          HandlerCarrier.file inner.2 input else inner.2) from by rw [hpure],
        cache_fileIf]]
    rw [LazyBudget.lazyAnswer] at hinner
    cases hcached : carrier.cache input with
    | some cached =>
      rw [hcached, support_pure, Set.mem_singleton_iff] at hinner
      rw [show inner.2 = carrier from by rw [hinner]]
      exact hcompat
    | none =>
      rw [hcached] at hinner
      cases hopen : openCache publicSeed (fun _ => True) table input with
      | some answer =>
        rw [hopen, support_pure, Set.mem_singleton_iff] at hinner
        rw [show inner.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [hinner]]
        show RedrawCell.Compatible publicSeed table (carrier.cache.cacheQuery input answer)
        intro probe value hvalue
        rw [RedrawCell.unionCache_cacheQuery_open publicSeed table carrier.cache input answer
          hopen]
        by_cases hprobe : probe = input
        · subst hprobe
          rw [QueryCache.cacheQuery_self] at hvalue
          rw [RedrawCell.unionCache_of_open publicSeed table carrier.cache probe answer hopen,
            hvalue]
        · rw [QueryCache.cacheQuery_of_ne _ _ hprobe] at hvalue
          exact hcompat probe value hvalue
      | none =>
        rw [hopen, support_map] at hinner
        obtain ⟨answer, -, heq⟩ := hinner
        rw [show inner.2 = HandlerCarrier.cacheAnswer carrier input answer from by rw [← heq]]
        show RedrawCell.Compatible publicSeed table (carrier.cache.cacheQuery input answer)
        intro probe value hvalue
        rw [RedrawCell.unionCache_cacheQuery_fresh publicSeed table carrier.cache input hopen]
        by_cases hprobe : probe = input
        · subst hprobe
          rw [QueryCache.cacheQuery_self] at hvalue
          rw [QueryCache.cacheQuery_self, hvalue]
        · rw [QueryCache.cacheQuery_of_ne _ _ hprobe] at hvalue
          rw [QueryCache.cacheQuery_of_ne _ _ hprobe]
          exact hcompat probe value hvalue

/-! ## The run -/

open scoped Classical in
/-- **The game's run is the serving handler's run at total availability.** -/
theorem probEvent_rom_eq_serving {α : Type} (publicSeed : Digest) (pk : PublicKey)
    (table : Cells × Padding) (event : α × QueryCache HashSpec → Prop)
    (computation : OracleComp OracleWorld α) :
    ∀ (carrier : HandlerCarrier.State) (record : List (Bytes × HandlerCarrier.State))
      (count : Nat),
      RedrawCell.Compatible publicSeed table carrier.cache →
        Pr[event | (simulateQ KeygenUniform.rom computation).run
            (RedrawCell.unionCache publicSeed table carrier.cache)] =
          Pr[fun z : α × HandlerState =>
              event (z.1, RedrawCell.unionCache publicSeed table z.2.1.cache) |
            (simulateQ (servingProgram publicSeed pk (fun _ _ => True) table) computation).run
              (carrier, record, count)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro carrier record count _
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure,
      probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    intro carrier record count hcompat
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      rom_union_step publicSeed pk table queried carrier record count hcompat,
      bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun step => ?_
    by_cases hmem : step ∈ support
        (((servingProgram publicSeed pk (fun _ _ => True) table) queried).run
          (carrier, record, count))
    · exact congrArg _ (ih step.1 step.2.1 step.2.2.1 step.2.2.2
        (compatible_step publicSeed pk table queried carrier record count hcompat step hmem))
    · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-! ## The tail at a drawn table, answered by the handler that files -/

open WalkTable TableTail HonestTail in
/-- The honest game at a drawn table, answered by the serving handler from nothing. -/
noncomputable def servingHandlerRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (state : HandlerState) :
    ProbComp (((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × HandlerState) :=
  (simulateQ (servingProgram publicSeed (keysOf prfSeed publicSeed table).2 (fun _ _ => True)
      table)
    (TouchedKeys.honestLinked adversary prfSeed publicSeed table)).run state

open WalkTable TableTail HonestTail in
/-- **The honest game's run is the serving handler's run, started from nothing.** -/
theorem probEvent_honest_serving (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding)
    (event : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[event | honestRun adversary prfSeed publicSeed table] =
      Pr[fun z => event (z.1, RedrawCell.unionCache publicSeed table z.2.1.cache) |
        servingHandlerRun adversary prfSeed publicSeed table
          (HandlerCarrier.empty, record, count)] := by
  rw [honestRun, servingHandlerRun,
    show (walkOfTable prfSeed publicSeed table).2 =
      RedrawCell.unionCache publicSeed table HandlerCarrier.empty.cache from by
      rw [HandlerCarrier.cache_empty, RedrawCell.unionCache_empty,
        walkOfTable_cache_eq_openCache]]
  exact probEvent_rom_eq_serving publicSeed (keysOf prfSeed publicSeed table).2 table event _
    HandlerCarrier.empty record count (RedrawCell.compatible_empty publicSeed table)

open WalkTable TableTail HonestTail WarmedGame in
/-- **The tail at a drawn table, as the serving handler's run.** The chain the charge reads:
honest throughout, with the keys handed in, the game one computation, and the handler the one
that files what the signer discloses. -/
theorem probEvent_tail_serving (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : Outcome × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[fun result => event (result.1.1, result.2) |
        tail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun z => event ((LinkedGame.outcomeOf z.1).1,
          RedrawCell.unionCache publicSeed table z.2.1.cache) |
        servingHandlerRun adversary prfSeed publicSeed table
          (HandlerCarrier.empty, record, count)] := by
  rw [probEvent_tail_honestLinked adversary prfSeed publicSeed table event,
    probEvent_honest_serving adversary prfSeed publicSeed table
      (fun result => event ((LinkedGame.outcomeOf result.1).1, result.2)) record count]

end SlhDsaSecurity.ServingTable

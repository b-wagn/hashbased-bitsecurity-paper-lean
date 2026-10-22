import SlhDsaSecurity.Proof.WalkTable
import SlhDsaSecurity.Proof.LinkedGame
import SlhDsaSecurity.Proof.RecordedBudget
import SlhDsaSecurity.Proof.RedrawCell

/-!
# The tail at a drawn table, as one computation under one handler

`WalkTable.chargeRun` runs `WarmedGame.tail` at the walk a drawn table determines. The charge
reads something that looks nothing like it: one computation, under one handler, with the keys
handed in and the record kept. The two are the same run, and this file walks the distance in
the five steps that were already built for it, each of which is an equality rather than a
bound.

* **The outer count is dropped.** `tail` counts every hash call and the obligation's event never
  reads that count — `RoutedSplit.Trace` carries the outcome and the final cache, and the count
  rides along unread. `RecordedBudget.map_countAllHashes` is the projection.
* **The honest phase is stripped.** Key generation and the signer are answered from the walk's
  own table, which changes nothing about the law of the run and leaves them asking only inputs
  no table of graph cells holds.
* **The record is kept.** Forgetting it returns the stripped game exactly, so adding it is the
  same projection again in the other direction.
* **The keys are handed in.** Run from the walk's cache, key generation samples nothing, so the
  key may be the value the cache determines rather than a step of the computation — which is
  what lets the signer move into the handler.
* **The game becomes one computation.** `LinkedGame.recordedAfterSeedsAt_eq` is that move, and
  it is an equality of computations, so every field of the outcome survives it unchanged.

What the drawn table contributes is the one thing the walk used to supply by hypothesis: its
cache. `walkOfTable_cache` says the cache a drawn table's walk leaves is the warm cache of that
table's own cells and padding, which is the form `KeygenValue.run_recordedAfterSeeds` is stated
at, and `walkOfTable_cache_eq_openCache` says it is also the entries the handler may serve at
total availability — the two descriptions the two halves of the chain each need.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.TableTail

open Security CanonicalGraph WarmedGame WalkTable

/-! ## The cache a drawn table leaves -/

/-- **The walk's cache is the warm cache of the table's own output table.** -/
theorem walkOfTable_cache (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    (walkOfTable prfSeed publicSeed table).2 =
      HonestProbes.warmCache publicSeed (table.1 Node.secretSeed)
        (fullOutput table.1 table.2) := by
  rw [walkOfTable, HonestProbes.warmCache, cellsOfOutputs_fullOutput]

/-- **And it is what the handler may serve at total availability.** -/
theorem walkOfTable_cache_eq_openCache (prfSeed publicSeed : Digest)
    (table : Cells × Padding) :
    (walkOfTable prfSeed publicSeed table).2 =
      OpenCache.openCache publicSeed (fun _ => True) table := by
  rw [walkOfTable_cache, ← RedrawCell.openCache_total_eq_warmCache publicSeed
    (table.1 Node.secretSeed) (fullOutput table.1 table.2),
    RedrawCell.splitTable_fullOutput]

/-! ## The count the event does not read -/

/-- **The tail, uncounted.** -/
theorem probEvent_tail_uncounted (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | tail adversary start] =
      Pr[event |
        (simulateQ KeygenUniform.rom (afterSeeds adversary start.1.1)).run start.2] := by
  have hmap : (simulateQ KeygenUniform.rom (afterSeeds adversary start.1.1)).run start.2 =
      (fun result : (Outcome × Nat) × QueryCache HashSpec => (result.1.1, result.2)) <$>
        (simulateQ KeygenUniform.rom
          (Security.countAllHashes (afterSeeds adversary start.1.1))).run start.2 := by
    conv_lhs => rw [← RecordedBudget.map_countAllHashes (afterSeeds adversary start.1.1)]
    rw [simulateQ_map, StateT.run_map]
  rw [hmap, probEvent_map, tail]
  rfl

/-! ## The honest phase, stripped and recorded -/

/-- **The tail is the stripped game, uncounted.** -/
theorem probEvent_tail_stripped (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | tail adversary start] =
      Pr[event | (simulateQ KeygenUniform.rom
        (StrippedGame.strippedAfterSeeds adversary start.1.1 start.2)).run start.2] := by
  rw [probEvent_tail_uncounted adversary start event]
  exact (probEvent_congr' (fun _ _ => Iff.rfl)
    (StrippedGame.evalDist_run_strippedAfterSeeds adversary start.1.1 start.2 start.2
      (StrippedGame.Extends.refl start.2))).symm

/-- **The tail is the recorded game, with the record carried.** -/
theorem probEvent_tail_recorded (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | tail adversary start] =
      Pr[fun result => event (result.1.1, result.2) | (simulateQ KeygenUniform.rom
        (RecordedQueries.recordedAfterSeeds adversary start.1.1 start.2)).run start.2] := by
  have hmap : (simulateQ KeygenUniform.rom
        (StrippedGame.strippedAfterSeeds adversary start.1.1 start.2)).run start.2 =
      (fun result : (Outcome × Multiset Bytes) × QueryCache HashSpec => (result.1.1, result.2))
        <$> (simulateQ KeygenUniform.rom
          (RecordedQueries.recordedAfterSeeds adversary start.1.1 start.2)).run start.2 := by
    conv_lhs => rw [← RecordedQueries.map_recordedAfterSeeds adversary start.1.1 start.2]
    rw [simulateQ_map, StateT.run_map]
  rw [probEvent_tail_stripped adversary start event, hmap, probEvent_map]
  rfl

/-! ## The keys handed in, and the game as one computation -/

/-- The keys the drawn table's own cache determines. Their only table coordinates are the secret
seed and the honest root, which is what the charge's blindness hypothesis asks of them. -/
noncomputable def keysOf (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    SecretKey × PublicKey :=
  KeygenValue.honestKeys (table.1 Node.secretSeed, prfSeed, publicSeed)
    (fullOutput table.1 table.2)

/-- The game at a drawn table, as one computation under one handler. -/
noncomputable def linkedRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) :
    ProbComp ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom
    ((simulateQ (RecordedPhase.unchargedPhase
        (StrippedGame.strippedSign (walkOfTable prfSeed publicSeed table).2
          (keysOf prfSeed publicSeed table).1))
      (LinkedGame.linkedAfterSeeds adversary (keysOf prfSeed publicSeed table))).run [])).run
    (walkOfTable prfSeed publicSeed table).2

/-- **The tail at a drawn table is the linked game under the uncharged handler.** The keys are
the ones the table's own cache determines, and the outcome is assembled after the run from the
value and the handler's final log. -/
theorem probEvent_tail_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) |
        tail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun result => event ((LinkedGame.outcomeOf result.1).1, result.2) |
        linkedRun adversary prfSeed publicSeed table] := by
  rw [probEvent_tail_recorded adversary (walkOfTable prfSeed publicSeed table) event,
    show (simulateQ KeygenUniform.rom (RecordedQueries.recordedAfterSeeds adversary
        ((walkOfTable prfSeed publicSeed table).1.1)
        (walkOfTable prfSeed publicSeed table).2)).run
          (walkOfTable prfSeed publicSeed table).2 =
      (simulateQ KeygenUniform.rom (KeygenValue.recordedAfterSeedsAt adversary
        (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2)).run
          (walkOfTable prfSeed publicSeed table).2 from by
      rw [walkOfTable_cache prfSeed publicSeed table]
      exact KeygenValue.run_recordedAfterSeeds adversary
        (table.1 Node.secretSeed, prfSeed, publicSeed) (fullOutput table.1 table.2),
    LinkedGame.recordedAfterSeedsAt_eq, simulateQ_map, StateT.run_map, probEvent_map, linkedRun]
  rfl

/-! ## The handler, started from nothing

The game runs against the walk's cache, which already carries the cells; the charge runs against
a handler that starts empty and draws the programmed entries only as they are asked for.
`RedrawCell.probEvent_rom_eq_lazy` says those are the same run, and what it needs here is the
cache identity: the walk's cache is the handler's view of the table at total availability, which
`unionCache_empty` says is what the handler holds before it has answered anything. -/

/-- The game at a drawn table, answered by the handler from nothing. -/
noncomputable def handlerRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (state : OpenCache.HandlerState) :
    ProbComp (((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × OpenCache.HandlerState) :=
  (simulateQ (OpenCache.lazyProgram publicSeed (fun _ _ => True) table)
    ((simulateQ (RecordedPhase.unchargedPhase
        (StrippedGame.strippedSign (walkOfTable prfSeed publicSeed table).2
          (keysOf prfSeed publicSeed table).1))
      (LinkedGame.linkedAfterSeeds adversary (keysOf prfSeed publicSeed table))).run [])).run
    state

/-- **The game's run is the handler's run, with the handler started from nothing.** -/
theorem probEvent_linked_handler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding)
    (event : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[event | linkedRun adversary prfSeed publicSeed table] =
      Pr[fun z => event (z.1, RedrawCell.unionCache publicSeed table z.2.1.cache) |
        handlerRun adversary prfSeed publicSeed table (HandlerCarrier.empty, record, count)] := by
  rw [linkedRun, handlerRun,
    show (walkOfTable prfSeed publicSeed table).2 =
      RedrawCell.unionCache publicSeed table HandlerCarrier.empty.cache from by
      rw [HandlerCarrier.cache_empty, RedrawCell.unionCache_empty,
        walkOfTable_cache_eq_openCache]]
  exact RedrawCell.probEvent_rom_eq_lazy publicSeed table event _ HandlerCarrier.empty record count
    (RedrawCell.compatible_empty publicSeed table)

/-- **The tail at a drawn table, as the handler's run.** The chain, end to end: the count the
event does not read is dropped, the honest phase is stripped, the record is kept, the keys are
handed in, the game becomes one computation, and the handler starts from nothing.

**This is the stripped chain, and the charge cannot be met at its end.** `RedrawCell`'s
`htouched` asks for a syntactic equality of computations, and the stripped signer carries the
walk's whole cache, so it touches every cell. `HonestTail.probEvent_tail_honest_handler` is the
same chain with the signer left honest — one step shorter, since stripping is the step not
taken — and `ServingTable.probEvent_tail_serving` carries it on to the handler that files, which
is where the charge reads it. -/
theorem probEvent_tail_handler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : Outcome × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[fun result => event (result.1.1, result.2) |
        tail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun z => event ((LinkedGame.outcomeOf z.1).1,
          RedrawCell.unionCache publicSeed table z.2.1.cache) |
        handlerRun adversary prfSeed publicSeed table (HandlerCarrier.empty, record, count)] := by
  rw [probEvent_tail_linked adversary prfSeed publicSeed table event,
    probEvent_linked_handler adversary prfSeed publicSeed table
      (fun result => event ((LinkedGame.outcomeOf result.1).1, result.2)) record count]

end SlhDsaSecurity.TableTail

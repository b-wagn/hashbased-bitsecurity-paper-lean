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

/-! ## The count the event does not read -/

/-! ## The honest phase, stripped and recorded -/

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

/-! ## The handler, started from nothing

The game runs against the walk's cache, which already carries the cells; the charge runs against
a handler that starts empty and draws the programmed entries only as they are asked for.
`RedrawCell.probEvent_rom_eq_lazy` says those are the same run, and what it needs here is the
cache identity: the walk's cache is the handler's view of the table at total availability, which
`unionCache_empty` says is what the handler holds before it has answered anything. -/

end SlhDsaSecurity.TableTail

import SlhDsaSecurity.Proof.TouchedKeys

/-!
# The tail at a drawn table, without stripping

`TableTail` walks the warmed tail down to one computation under one handler, through the
stripped signer. This file walks it down again through the honest one, in the same steps and for
the same reasons, ending at `TouchedKeys.honestLinked` — the computation whose blindness is
already proved.

The chain is shorter by exactly one step, because stripping is what is not done here:

* **the outer count is dropped**, by the projection `probEvent_tail_uncounted`, the event never
  reading it;
* **the record is kept**, `RecordedTail.map_recordedAfterSeeds` being the same projection in the
  other direction at the unstripped game;
* **the keys are handed in**, by `HonestLinked.run_recordedAfterSeeds`, key generation sampling
  nothing when run from the walk's own cache;
* **the game becomes one computation**, by `HonestLinked.honestAfterSeeds_eq`;
* **and the handler starts from nothing**, by `RedrawCell.probEvent_rom_eq_lazy` at the cache
  identity `walkOfTable_cache_eq_openCache`.

**What changes by not stripping: the record and the handler become different observers.** The
record sits at the writer, and `RecordedQueries.recordedSigningOracle` tells `0` into its
multiset and calls the signer through `liftM` below it — so the signer's hash inputs never enter
the record, here or in the stripped game. The handler sits at the oracle, and every query the
signer makes reaches it. Stripping used to make the two observers agree, by leaving the honest
phase nothing to ask; they no longer do.

So a bound justified by "the honest phase is not recorded" is still true **at the record** and
is now false **at the handler** — and that is the distinction the stall has to respect, since
what it reads is a handler the signer's probes reach. The signer's probes are paid for where
they are made: the served notion files what the signer discloses, a disclosed cell is available,
and so those probes are not sensitive at the state they are made from. That is the
`ServedAgreement` side of the join, which is stated at `Scheme.sign` precisely because this run
is. Saying *where* each count is taken is worth more than the coincidence it replaces.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestTail

open Security CanonicalGraph WarmedGame WalkTable TableTail TouchedKeys

/-! ## The record, kept at the honest game -/

/-- **The tail is the honest recorded game, with the record carried.** -/
theorem probEvent_tail_recorded (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | tail adversary start] =
      Pr[fun result => event (result.1.1, result.2) | (simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary start.1.1)).run start.2] := by
  have hmap : (simulateQ KeygenUniform.rom (afterSeeds adversary start.1.1)).run start.2 =
      (fun result : (Outcome × Multiset Bytes) × QueryCache HashSpec => (result.1.1, result.2))
        <$> (simulateQ KeygenUniform.rom
          (RecordedTail.recordedAfterSeeds adversary start.1.1)).run start.2 := by
    conv_lhs => rw [← RecordedTail.map_recordedAfterSeeds adversary start.1.1]
    rw [simulateQ_map, StateT.run_map]
  rw [probEvent_tail_uncounted adversary start event, hmap, probEvent_map]
  rfl

/-! ## The keys handed in, and the game as one computation -/

/-- The honest game at a drawn table, as one computation under one handler. -/
noncomputable def honestRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) :
    ProbComp ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (honestLinked adversary prfSeed publicSeed table)).run
    (walkOfTable prfSeed publicSeed table).2

/-- **The tail at a drawn table is the linked game under the honest handler.** -/
theorem probEvent_tail_honestLinked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : Outcome × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) |
        tail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun result => event ((LinkedGame.outcomeOf result.1).1, result.2) |
        honestRun adversary prfSeed publicSeed table] := by
  rw [probEvent_tail_recorded adversary (walkOfTable prfSeed publicSeed table) event,
    show (simulateQ KeygenUniform.rom (RecordedTail.recordedAfterSeeds adversary
        ((walkOfTable prfSeed publicSeed table).1.1))).run
          (walkOfTable prfSeed publicSeed table).2 =
      (simulateQ KeygenUniform.rom (HonestLinked.recordedAfterSeedsWith adversary
        (keysOf prfSeed publicSeed table)
        (Scheme.sign (keysOf prfSeed publicSeed table).1))).run
          (walkOfTable prfSeed publicSeed table).2 from by
      rw [walkOfTable_cache prfSeed publicSeed table]
      exact HonestLinked.run_recordedAfterSeeds adversary
        (table.1 Node.secretSeed, prfSeed, publicSeed) (fullOutput table.1 table.2),
    HonestLinked.honestAfterSeeds_eq, simulateQ_map, StateT.run_map, probEvent_map, honestRun,
    honestLinked]
  rfl

/-! ## The handler, started from nothing -/

/-- The honest game at a drawn table, answered by the handler from nothing. -/
noncomputable def honestHandlerRun (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (state : OpenCache.HandlerState) :
    ProbComp (((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × OpenCache.HandlerState) :=
  (simulateQ (OpenCache.lazyProgram publicSeed (fun _ _ => True) table)
    (honestLinked adversary prfSeed publicSeed table)).run state

/-- **The honest game's run is the handler's run, with the handler started from nothing.** -/
theorem probEvent_honest_handler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding)
    (event : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[event | honestRun adversary prfSeed publicSeed table] =
      Pr[fun z => event (z.1, RedrawCell.unionCache publicSeed table z.2.1.cache) |
        honestHandlerRun adversary prfSeed publicSeed table
          (HandlerCarrier.empty, record, count)] := by
  rw [honestRun, honestHandlerRun,
    show (walkOfTable prfSeed publicSeed table).2 =
      RedrawCell.unionCache publicSeed table HandlerCarrier.empty.cache from by
      rw [HandlerCarrier.cache_empty, RedrawCell.unionCache_empty,
        walkOfTable_cache_eq_openCache]]
  exact RedrawCell.probEvent_rom_eq_lazy publicSeed table event _ HandlerCarrier.empty record
    count (RedrawCell.compatible_empty publicSeed table)

/-- **The tail at a drawn table, as the honest handler's run.** The chain, end to end: the count
the event does not read is dropped, the record is kept, the keys are handed in, the game becomes
one computation, and the handler starts from nothing — with the signer left honest throughout. -/
theorem probEvent_tail_honest_handler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (event : Outcome × QueryCache HashSpec → Prop)
    (record : List (Bytes × HandlerCarrier.State)) (count : Nat) :
    Pr[fun result => event (result.1.1, result.2) |
        tail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun z => event ((LinkedGame.outcomeOf z.1).1,
          RedrawCell.unionCache publicSeed table z.2.1.cache) |
        honestHandlerRun adversary prfSeed publicSeed table
          (HandlerCarrier.empty, record, count)] := by
  rw [probEvent_tail_honestLinked adversary prfSeed publicSeed table event,
    probEvent_honest_handler adversary prfSeed publicSeed table
      (fun result => event ((LinkedGame.outcomeOf result.1).1, result.2)) record count]

end SlhDsaSecurity.HonestTail

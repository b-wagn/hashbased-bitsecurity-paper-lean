import SlhDsaSecurity.Proof.LinkedGame
import SlhDsaSecurity.Proof.RecordedTail

/-!
# The same two moves, at the honest signer

`KeygenValue.run_recordedAfterSeeds` hands the keys in and `LinkedGame.recordedAfterSeedsAt_eq`
undoes the nesting, both at `StrippedGame.strippedSign`. The charge's last hypothesis cannot be
met there: `RedrawCell`'s `htouched` asks for a **syntactic** equality of computations, and the
stripped signer's `warm` is the whole table, so every cell is a name it touches. The unstripped
`Scheme.sign sk` reads no cache at all, so what it touches is `RedrawCell.seedAndRoot` — the two
names `KeygenValue.honestKeys` already says the key is built from. `ServedAgreement`'s agreement
is likewise proved at `Scheme.sign`, not at the stripped signer.

So the two moves are made again here, at the game `RecordedTail.recordedAfterSeeds` — the
recorded presentation of `WarmedGame.afterSeeds`, with the real `Scheme.keygenInternal` and
`Scheme.sign`.

Neither move is a copy. `recordedAfterSeedsWith` is `KeygenValue.recordedAfterSeedsAt` with the
signer taken as a parameter rather than fixed, the stripped game is that definition at the
stripped signer by `rfl`, and the linking law is proved once for every signer: `run_phase_counted`
and `run_unchargedPhase_lift` are both already stated at an arbitrary one, and nothing in the
nesting ever looked at which signer was being nested. The honest instances are then what this
half takes onward, and the stripped statements keep their exact shapes for their existing
readers.

**Key generation is substituted the same way and for the same reason.** Run from the walk's
cache it samples nothing, so `HonestProbes.run_keygenInternal_world_eq_pure` replaces the call by
its value; the law below is again about the **uncounted** run, with `Security.countAllHashes`
left outside it, because the substitution does change the outer total — it removes hash calls
that total counts. Apply it under the counter and it would be claiming something false.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestLinked

open Security RecordedQueries RecordedPhase KeygenValue LinkedGame

/-! ## The game with its keys and its signer handed in -/

/-- The recorded game with its keys handed in and its signer a parameter. -/
noncomputable def recordedAfterSeedsWith (adversary : Adversary)
    (keys : SecretKey × PublicKey) (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    OracleComp OracleWorld (Outcome × Multiset Bytes) := do
  let adversaryStep ←
    (simulateQ (recordedAdversaryImpl + recordedSigningOracle signer)
      (adversary.main keys.2)).run.run []
  let verifierStep ← countRecorded verifierCost
    (Scheme.verify keys.2 adversaryStep.1.1.message adversaryStep.1.1.signature)
  pure ({
    forgery := adversaryStep.1.1
    signed := adversaryStep.2
    verified := verifierStep.1
    counts := (Multiplicative.toAdd adversaryStep.1.2).1 + verifierStep.2.1 },
    (Multiplicative.toAdd adversaryStep.1.2).2 + verifierStep.2.2)

/-- The stripped game with its keys handed in is this one at the stripped signer. -/
theorem recordedAfterSeedsAt_eq_with (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) :
    recordedAfterSeedsAt adversary keys warm =
      recordedAfterSeedsWith adversary keys (StrippedGame.strippedSign warm keys.1) :=
  rfl

/-! ## Undoing the nesting, at any signer -/

/-- **The game is one computation under one handler**, for whichever signer it was written at.
An equality of computations, so the outcome and the record come out as the same values. -/
theorem recordedAfterSeedsWith_eq (adversary : Adversary) (keys : SecretKey × PublicKey)
    (signer : Message → OracleComp OracleWorld (Option Bytes)) :
    recordedAfterSeedsWith adversary keys signer =
      outcomeOf <$> (simulateQ (unchargedPhase signer)
        (linkedAfterSeeds adversary keys)).run [] := by
  rw [recordedAfterSeedsWith, linkedAfterSeeds, simulateQ_bind, StateT.run_bind,
    ← run_phase_counted, map_bind]
  refine bind_congr fun adversaryStep => ?_
  rw [simulateQ_bind, StateT.run_bind, run_unchargedPhase_lift, bind_map_left, map_bind]
  refine bind_congr fun verifierStep => ?_
  rw [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

/-! ## The honest instances -/

/-- **Generating the keys and handing them in are the same run**, at the honest signer. -/
theorem run_recordedAfterSeeds (adversary : Adversary) (sds : Digest × Digest × Digest)
    (outputs : CanonicalGraph.Programming.Outputs) :
    (simulateQ KeygenUniform.rom (RecordedTail.recordedAfterSeeds adversary sds)).run
        (HonestProbes.warmCache sds.2.2 sds.1 outputs) =
      (simulateQ KeygenUniform.rom
        (recordedAfterSeedsWith adversary (honestKeys sds outputs)
          (Scheme.sign (honestKeys sds outputs).1))).run
        (HonestProbes.warmCache sds.2.2 sds.1 outputs) := by
  rw [RecordedTail.recordedAfterSeeds, simulateQ_bind, StateT.run_bind,
    HonestProbes.run_keygenInternal_world_eq_pure, pure_bind]
  rfl

/-- **The honest game is one computation under the honest handler.** -/
theorem honestAfterSeeds_eq (adversary : Adversary) (keys : SecretKey × PublicKey) :
    recordedAfterSeedsWith adversary keys (Scheme.sign keys.1) =
      outcomeOf <$> (simulateQ (unchargedPhase (Scheme.sign keys.1))
        (linkedAfterSeeds adversary keys)).run [] :=
  recordedAfterSeedsWith_eq adversary keys (Scheme.sign keys.1)

end SlhDsaSecurity.HonestLinked

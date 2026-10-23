import SlhDsaSecurity.Proof.CarrierSignRecord
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.CarrierTailRecordings

/-!
# Every target-recorded input of the carrier tail is a query the record holds

`LateProvenance.hrecord` at the tail the obligations are moving to. The shape of the argument is
the one that file already has — the game splits at its three sequencing points and each branch
asks its question of the object that can answer it — and only the signer's two branches differ.

**Both differ by reading the flag instead of the bytes.** The randomiser probe is excluded by
`AnswerCarrier.not_carrierRightKeep_randomizerInput`, which compares against the frame in
flight rather than against a syntactic class; the digest probe by
`HandlerCarrier.FilesLeft` holding at the carrier it was filed at, which is what the sub-run's
framing and its queries were carried out for.

This is the input to the bracketed containment, not the plug for the shared assembly's socket:
`LateProbes.probes_le_recordMessageClass` is what takes it, and the socket a layer up takes the
ordering charge's conclusion instead.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierRecord

open Security BracketedRun CarrierFiles CarrierRecordings CarrierSignRecord
  CarriedWitness CarrierTail RecordedQueries AnswerCarrier

/-! ## The key the run generated is the one the walk fixed

Key generation at the warm cache is a `pure`, so both facts the signer's branches need come off
the walk directly and neither has to be matched against anything. -/

set_option maxHeartbeats 1000000 in
theorem keys_eq_replay (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0)))) :
    keys.1 = @Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery walk.2)
      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 := by
  obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
  have hrom := mem_support_rom_of_carrier (keyAt walk) (rightKeep walk) _
    (startAt walk.2, (([], []), 0)) keys hkeys
  rw [show (startAt walk.2, (([], []), (0 : Nat))).1.cache = walk.2 from rfl, hwarm,
    HonestProbes.run_keygenInternal_world_eq_pure, support_pure, Set.mem_singleton_iff] at hrom
  rw [hwarm]
  exact (Prod.ext_iff.mp hrom).1

theorem keys_publicKey (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0)))) :
    keys.1.1.publicKey = keyAt walk := by
  rw [keys_eq_replay rightKeep walk hwalk keys hkeys]
  exact LateProvenance.keygen_publicKey walk.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2

/-! ## The assembly -/

end SlhDsaSecurity.CarrierRecord

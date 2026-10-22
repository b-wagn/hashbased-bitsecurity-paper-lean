import SlhDsaSecurity.Proof.CarrierPhaseRecord
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

open Security BracketedRun CarrierFiles CarrierRecordings CarrierSignRecord CarrierPhaseRecord
  CarriedWitness CarrierTail RecordedQueries AnswerCarrier

set_option maxHeartbeats 1000000 in
/-- **The signer's digest probe is filed on the left, so it is not a target.** The flag is up for
the request the sub-run is serving, and the probe is that request's own digest input — so the
disclosing test holds at the carrier the entry would have been filed at, and the target test
denies exactly that. -/
theorem not_carrierRightKeep_digest (walk : Walk) (sk : SecretKey)
    (hpk : sk.publicKey = keyAt walk) (framed : Bytes) (answer : HashOutput)
    (mid : HandlerCarrier.State) (hframing : mid.framing = some framed)
    (entry : Bytes × HashOutput)
    (hdigest : entry.1 = Hashing.messageInput (Hashing.truncate answer) sk.publicKey framed) :
    ¬ carrierRightKeep walk entry.1 (servingNotice (keyAt walk) mid entry.1) := by
  rintro ⟨-, hnotFiled⟩
  refine hnotFiled ⟨framed, ?_, Hashing.truncate answer, ?_⟩
  · rw [framing_servingNotice]
    exact hframing
  · rw [hdigest, hpk]

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

theorem keys_prf (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    (keys : (SecretKey × PublicKey) × CountedState)
    (hkeys : keys ∈ support ((simulateQ (handlerAt rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
        (startAt walk.2, (([], []), 0)))) :
    keys.1.1.prf = walk.1.1.2.1 := by
  rw [keys_eq_replay rightKeep walk hwalk keys hkeys]
  exact LateProvenance.keygen_prf walk.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2

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

set_option maxHeartbeats 1000000 in
/-- **Every target-recorded input of the carrier tail is a query the record holds**, with no
hypothesis.

The tail splits at its three sequencing points and each branch asks its question of the object
that can answer it. Key generation's and the verifier's are about an input's shape and about who
asked, so those sub-runs project to the shared oracle and the lemmas already proved there
answer. The adversary's phase is about the *recording*, so it is asked of the recorder, and its
signer branch is asked of the signer's own sub-run — which hands back the view each entry was
filed at, and both of the signer's own probes are refuted at a view.

**The two signer branches read the flag, not the bytes.** On the cache route the randomiser
probe was excluded by `¬ RandomizerGate.PrfClass` in the narrowed class and the digest probe by
`CacheAvailability.SignerRandomised` at the cache. Here both are excluded by the framing in
flight: `AnswerCarrier.not_carrierRightKeep_randomizerInput` at the view the probe was filed at,
and `not_carrierRightKeep_digest` at the carrier the sub-run reached. That is why the sub-run
lemmas carry views rather than cache values.

Each stage is read at its *own* cache. Nothing here needs an entry filed early to survive to the
end, because every fact a branch uses is a fact about the stage that filed it. -/
theorem hrecord (adversary : Adversary) :
    ∀ pair ∈ support (LateProbes.pairedOf (carrierTail carrierRightKeep) adversary),
      Target.GoodWalk pair.1 → ∀ entry ∈ pair.2.2.2.2,
        entry.1 ∈ SharedJoin.recordOf (LateProbes.forgetRecordings pair) := by
  classical
  intro pair hpair hgood entry hentry
  obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := LateProbes.mem_support_pairedOf hpair
  subst hvalue
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  -- The entry is of the message class, because the target test keeps nothing else.
  have hmessage : CombinedCharge.IsMessageInput (keyAt walk) entry.1 :=
    CarrierTailRecordings.recordClass_carrierTail carrierRightKeep
      (fun walk input => CombinedCharge.IsMessageInput (keyAt walk) input)
      (fun walk input view hright => carrierRightKeep_class walk input view hright)
      adversary walk result hresult entry hentry
  -- The tail, split at its three sequencing points.
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest1⟩ := hresult
  rw [mem_support_bind_iff] at hrest1
  obtain ⟨middle, hmiddle, hrest2⟩ := hrest1
  rw [mem_support_bind_iff] at hrest2
  obtain ⟨final, hfinal, hpure⟩ := hrest2
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hprf : keys.1.1.prf = walk.1.1.2.1 := keys_prf carrierRightKeep walk hwalk keys hkeys
  have hpk : keys.1.1.publicKey = keyAt walk :=
    keys_publicKey carrierRightKeep walk hwalk keys hkeys
  have hrecordEq : result.1.1.2 = (Multiplicative.toAdd middle.2.1).2 + final.1.2.2 := by
    rw [hpure]
  rw [show result.2 = forgetCarrier final.2 from by rw [hpure]] at hentry
  show entry.1 ∈ result.1.1.2
  rw [hrecordEq]
  rcases verify_right_record (keyAt walk) (carrierRightKeep walk) keys.1.2 middle.1.message
      middle.1.signature middle.2.2.2 final hfinal entry hentry with hphaseMem | hrec
  · rcases right_record_phase (keyAt walk) (carrierRightKeep walk) keys.1.1
        (adversary.main keys.1.2) (1 : Multiplicative Tally) [] keys.2 middle hmiddle
        middle.2.2.2.1.cache (fun _ _ hprobe => hprobe) entry hphaseMem with hkeyMem | hsource
    · -- Key generation's probes are canonical, which a message input is not.
      rcases keygen_right_record (keyAt walk) (carrierRightKeep walk) walk.1.1.1 walk.1.1.2.1
          walk.1.1.2.2 (startAt walk.2, (([], []), 0)) keys hkeys keys.2.1.cache
          (fun _ _ hprobe => hprobe) entry hkeyMem with hstart | hkeygenQuery
      · exact absurd hstart (by simp)
      · obtain ⟨randomizer, message, hinput⟩ := hmessage
        obtain ⟨parent, hparent⟩ :=
          HonestProbes.probes_keygenInternal keys.2.1.cache walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
            entry.1 hkeygenQuery
        exact absurd (hinput ▸ hparent)
          (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
    · rcases hsource with hrecMem |
        ⟨framed, ⟨hrandomiser, view, hviewFraming, hviewKeep⟩ |
          ⟨mid, answer, -, -, -, hkeep, hframing, hqueries⟩⟩
      · exact Multiset.mem_add.mpr (Or.inl hrecMem)
      · -- The signer's own randomiser probe, refuted at the view it was filed at.
        refine absurd hviewKeep ?_
        rw [hrandomiser, hprf, hpk]
        exact not_carrierRightKeep_randomizerInput walk view framed hviewFraming
      · -- Its digest probe, refuted at the carrier the sub-run reached.
        rcases SignerRandomiser.probes_signInternalAt middle.2.2.2.1.cache
            (Hashing.truncate answer) keys.1.1 framed entry.1 hqueries with
          ⟨parent, hparent⟩ | hdigest
        · obtain ⟨randomizer, message, hinput⟩ := hmessage
          exact absurd (hinput ▸ hparent)
            (HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent))
        · exact absurd hkeep (not_carrierRightKeep_digest walk keys.1.1 hpk framed answer mid
            hframing entry hdigest)
  · exact Multiset.mem_add.mpr (Or.inr hrec)

end SlhDsaSecurity.CarrierRecord

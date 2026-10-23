import SlhDsaSecurity.Proof.BySourceAnswer
import SlhDsaSecurity.Proof.CarrierRecord

/-!
# The answer half's counts, without the requests

`BySourceAnswer.fresh_add_right_le` bounds the structural faults' fresh entries and the target
record by `work + requests`. The requests are there only because the count went through
`freshMass (Deviating ∨ Targeted)`, and a signer's digest input is a fresh `Targeted` entry. It is
never a structural fault, though, and never a target entry: the target recording files only the
adversary's and the verifier's queries (`CarrierRecord.hrecord`).

So both counts are inside the record:

  `fresh faults + target entries ≤ |record| ≤ work`,

pathwise, with nothing charged to a signing request.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerNoRequests

open Security CacheReplay CanonicalGraph BracketedRun CarrierTail CarrierThin FreshExpectation
  BySourceBridge BySourceAnswer

/-! ## The fresh faults are the record's -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries RecordedTail.recordedAfterSeeds

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
/-- **Every fresh structural-fault entry is a query of the record.** Key generation and the
signer install only canonical inputs, their `PRF_msg` inputs and their digest inputs, and none of
those can carry a structural fault. -/
theorem deviating_mem_record (adversary : Adversary) {walk : Walk}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk))
    (input : Bytes) (hdeviating : Deviating walk input) (hnone : walk.2 input = none)
    (hfinal : result.2 input ≠ none) : input ∈ result.1.1.2 := by
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) :=
    hresult
  have hextends : ∀ (input : Bytes) (output : HashOutput), walk.2 input = some output →
      result.2 input = some output := fun input output hentry =>
    GrowthCharge.cache_value_persists _ walk.2 result.2 result.1 hrun input output hentry
  obtain ⟨keys, hkeys, hsource⟩ :=
    LateProvenance.provenance_recordedAfterSeeds adversary walk.1.1 walk.2 result hrun
  obtain ⟨hprf, hsecret, hpublicSeed⟩ : keys.1.prf = walk.1.1.2.1 ∧ keys.1.seed = walk.1.1.1 ∧
      keys.1.publicKey.seed = walk.1.1.2.2 := by
    rw [hkeys]
    exact keygen_seeds result.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
  have hcanonical : ∀ parent : StructuralNode, input ≠ canonicalInput walk.1.1.2.2
      (HonestProbes.replayCells result.2 walk.1.1.1 walk.1.1.2.2) parent := fun parent heq =>
    not_deviating_canonical hwalk result.2 hextends parent (heq ▸ hdeviating)
  -- A message input at the walk's key is never a structural fault.
  have hnotMessage : ¬ CombinedCharge.IsMessageInput (keyAt walk) input := fun hmessage =>
    hdeviating (CombinedCharge.separated_of_not_possible walk.1.1.2.2 (keyAt walk) walk.1.2
      hpublic withinBounds_structural input hmessage)
  rcases hsource input hnone hfinal with hrecord | hkeygen | ⟨entry, -, hmade⟩
  · exact hrecord
  · obtain ⟨parent, hparent⟩ := HonestProbes.probes_keygenInternal result.2 walk.1.1.1
      walk.1.1.2.1 walk.1.1.2.2 input hkeygen
    exact absurd hparent (hcanonical parent)
  · cases hframe : entry.1.frame with
    | none =>
      exact absurd (HonestProbes.probes_sign_none result.2 keys.1 entry.1 hframe (fun _ => False)
        input hmade.1) id
    | some framed =>
      rcases HonestProbes.probes_sign result.2 keys.1 entry.1 framed hframe input hmade.1 with
        ⟨parent, hparent⟩ | hrandomizer | hdigest
      · rw [hpublicSeed, hsecret] at hparent
        exact absurd hparent (hcanonical parent)
      · rw [hprf] at hrandomizer
        exact absurd (hrandomizer ▸ hdeviating) (not_deviating_randomizerInput walk hgood _ framed)
      · have hpk : keys.1.publicKey = keyAt walk := by
          rw [hkeys, LateProvenance.keygen_publicKey]
          exact AnswerSide.generatedKey_eq_walk adversary hwalk
            (RecordedTail.mem_support_tail_of_recorded adversary hresult)
        exact absurd ⟨HonestProbes.replayRandomizer result.2 keys.1 framed, framed,
          by rw [hdigest, hpk]⟩ hnotMessage

/-! ## At the split tail -/

attribute [local irreducible] WarmedGame.afterSeeds

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The fresh faults and the target record together are within the work**, on every run of
the split tail, whatever the signer is asked. -/
theorem fresh_add_right_le_work (adversary : Adversary) {walk : Walk}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts)
    (hz : z ∈ support (SplitTail.splitCarrierTail
      (CombinedCharge.IsMessageInput (keyAt walk)) QueryKind.hash QueryKind.verification
      keep127 adversary walk)) :
    freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞) ≤
      (z.1.1.1.1.counts.work : ℝ≥0∞) := by
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  -- The run, read at the recorded tail.
  have hcounted : ((z.1.1.1, z.2), z.1.2.1) ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (ClassGrowth.splitCost (CombinedCharge.IsMessageInput (keyAt walk))
        QueryKind.hash QueryKind.verification)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) := by
    rw [← SplitCarrierTail.forget_splitCarrierTail _ _ _ keep127 adversary walk, support_map]
    exact ⟨z, hz, rfl⟩
  have hrecorded := ClassGrowth.mem_support_countAllHashes_of_splitCost _
    AnswerFired.hash_ne_verification _ walk.2 _ hcounted
  -- The target record, read at the carrier tail.
  have hcarrier : z.1 ∈ support (carrierTail keep127 adversary walk) := by
    rw [← SplitTail.map_splitCarrierTail _ AnswerFired.hash_ne_verification keep127 adversary
      walk, support_map]
    exact ⟨z, hz, rfl⟩
  obtain ⟨hcached, hnodup⟩ :=
    CarrierTailRecordings.recordFreshNodup_carrierTail keep127 adversary walk z.1 hcarrier
  have hclass := CarrierTailRecordings.recordClass_carrierTail keep127 Targeted
    targeted_of_keep127 adversary walk z.1 hcarrier
  have hpaired : (walk, z.1) ∈ support (LateProbes.pairedOf (carrierTail keep127) adversary) := by
    unfold LateProbes.pairedOf
    rw [mem_support_bind_iff]
    refine ⟨walk, hwalk, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨z.1, hcarrier, by simp⟩
  have hinRecord := CarrierRecord.hrecord keep127 (fun _ _ _ hkeep => hkeep.1) adversary
    (walk, z.1) hpaired hgood
  -- Both classes, inside the record.
  let rightInputs : List Bytes := z.1.2.2.2.map Prod.fst
  have hright : (rightInputs.length : ℝ≥0∞) ≤
      freshMass (fun input => input ∈ rightInputs) walk.2 z.1.2.1 := by
    refine length_le_freshMass _ _ _ _ hnodup fun input hinput => ?_
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hinput
    refine ⟨hinput, ?_, hcached entry hentry⟩
    cases hwarm : walk.2 entry.1 with
    | none => rfl
    | some value =>
      obtain ⟨parent, hparent⟩ := WarmedCharges.walk_cache_canonical hwalk entry.1
        (by rw [hwarm]; simp)
      exact absurd (hparent ▸ hclass entry hentry) (not_targeted_canonical walk hpublic _ _ _)
  have hdisjoint : ∀ input, Deviating walk input → ¬ input ∈ rightInputs := by
    intro input hdeviating hinput
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hinput
    exact not_deviating_of_targeted walk hpublic entry.1 (hclass entry hentry) hdeviating
  have hheld := freshMass_le_card (fun input => Deviating walk input ∨ input ∈ rightInputs)
    walk.2 z.1.2.1 (Multiset.toFinset z.1.1.1.2) fun input hclassOf hnone hfinal => by
      rw [Multiset.mem_toFinset]
      rcases hclassOf with hdeviating | hinput
      · exact deviating_mem_record adversary hwalk hgood _ hrecorded input hdeviating hnone hfinal
      · obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hinput
        exact hinRecord entry hentry
  have hcard := RecordedTail.card_toFinset_le_count adversary hrecorded
  rw [List.length_map] at hright
  calc freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞)
      ≤ freshMass (Deviating walk) walk.2 z.1.2.1 +
          freshMass (fun input => input ∈ rightInputs) walk.2 z.1.2.1 :=
        add_le_add le_rfl hright
    _ = freshMass (fun input => Deviating walk input ∨ input ∈ rightInputs) walk.2 z.1.2.1 :=
        freshMass_add _ _ _ _ hdisjoint
    _ ≤ ((Multiset.toFinset z.1.1.1.2).card : ℝ≥0∞) := hheld
    _ ≤ (z.1.1.1.1.counts.work : ℝ≥0∞) := by exact_mod_cast hcard

end SlhDsaSecurity.AnswerNoRequests

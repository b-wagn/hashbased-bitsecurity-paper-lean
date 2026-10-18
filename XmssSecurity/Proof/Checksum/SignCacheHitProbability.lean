import XmssSecurity.Proof.Checksum.EncodingTargetMap
import XmssSecurity.Proof.Checksum.SigningRandomnessUniformity
import Mathlib.Data.Set.Card.Arithmetic

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def cachedEncodingEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) : ℝ≥0∞ :=
  (({entry ∈ cache.toSet |
    encodingInputLeafIndex? parameter entry.1 = some leafIndex}.encard : ENat) : ℝ≥0∞)

def cachedEncodingInputSet (cache : QueryCache HashSpec)
    (parameter : PublicParameter) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | (encodingInputLeafIndex? parameter entry.1).isSome}

noncomputable def cachedEncodingInputCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) : ℝ≥0∞ :=
  ((cachedEncodingInputSet cache parameter).encard : ENat)

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem cachedEncodingInputSet_cacheQuery_subset
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : HashOutput) :
    cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
      if (encodingInputLeafIndex? parameter input).isSome then
        insert ⟨input, output⟩ (cachedEncodingInputSet cache parameter)
      else
        cachedEncodingInputSet cache parameter := by
  intro entry hentry
  have hinsert := QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1
  rw [Set.mem_insert_iff] at hinsert
  cases hleafIndex : encodingInputLeafIndex? parameter input with
  | some leafIndex =>
    simp only [Option.isSome_some, if_true, Set.mem_insert_iff]
    rcases hinsert with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rcases hinsert with heq | hold
    · subst entry
      have hisSome := hentry.2
      change (encodingInputLeafIndex? parameter input).isSome = true at hisSome
      rw [hleafIndex] at hisSome
      exact Bool.noConfusion hisSome
    · exact ⟨hold, hentry.2⟩

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem cachedEncodingInputCount_cacheQuery_le
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : HashOutput) :
    cachedEncodingInputCount (cache.cacheQuery input output) parameter ≤
      cachedEncodingInputCount cache parameter +
        if (encodingInputLeafIndex? parameter input).isSome then 1 else 0 := by
  unfold cachedEncodingInputCount
  let newEntry : (t : HashSpec.Domain) × HashSpec.Range t := ⟨input, output⟩
  have hsubset :=
    cachedEncodingInputSet_cacheQuery_subset cache parameter input output
  cases hleafIndex : encodingInputLeafIndex? parameter input with
  | some leafIndex =>
    have hsubset' :
        cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
          insert newEntry (cachedEncodingInputSet cache parameter) := by
      simpa [hleafIndex, newEntry] using hsubset
    have hmono := Set.encard_mono hsubset'
    have hinsert := Set.encard_insert_le
      (cachedEncodingInputSet cache parameter) newEntry
    have hencard :
        (cachedEncodingInputSet (cache.cacheQuery input output) parameter).encard ≤
          (cachedEncodingInputSet cache parameter).encard + 1 := hmono.trans hinsert
    have hcast := ENat.toENNReal_mono hencard
    simpa [hleafIndex, ENat.toENNReal_add] using hcast
  | none =>
    have hsubset' :
        cachedEncodingInputSet (cache.cacheQuery input output) parameter ⊆
          cachedEncodingInputSet cache parameter := by
      simpa [hleafIndex] using hsubset
    have hencard :
        (cachedEncodingInputSet (cache.cacheQuery input output) parameter).encard ≤
          (cachedEncodingInputSet cache parameter).encard :=
      Set.encard_mono hsubset'
    have hcast := ENat.toENNReal_mono hencard
    simpa [hleafIndex] using hcast

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem uniform_signingRandomness_encodingInput_cacheHit_le_cachedEncodingEntryCount
    (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness)) =
        some output |
      $ᵗ Randomness] ≤
      cachedEncodingEntryCount cache parameter leafIndex *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (Concrete.CacheView.encodingInput parameter leafIndex (message, randomness)) =
      some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := {entry ∈ cache.toSet |
    encodingInputLeafIndex? parameter entry.1 = some leafIndex}
  have hcard : (targets.card : ℝ≥0∞) ≤ cachedEncodingEntryCount cache parameter leafIndex := by
    let embedding : (targets : Set Randomness) ↪ fiber :=
      ⟨fun randomness =>
          ⟨⟨Concrete.CacheView.encodingInput parameter leafIndex
                (message, randomness.1),
              Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
            ⟨Classical.choose_spec (Finset.mem_filter.mp randomness.2).2, by simp⟩⟩,
        fun left right heq => Subtype.ext <| congrArg Prod.snd <|
          Concrete.CacheView.encodingInput_injective parameter leafIndex <|
            congrArg (fun entry : fiber => entry.1.1) heq⟩
    simpa only [cachedEncodingEntryCount, fiber,
      Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      ENat.toENNReal_mono embedding.encard_le
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ℝ≥0∞) *
      ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ ≤ _
  exact mul_le_mul' hcard le_rfl

/-- Running one signing query samples its 128-bit randomness first, without changing the random-oracle cache, and then performs the fixed-randomness signing attempt. -/
theorem Concrete.sign_run_eq
    (secretKey : SecretKey)
    (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.sign secretKey leafIndex message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))).run cache) := by
  rw [Concrete.sign_eq, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl
        (liftM Concrete.signingRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$>
          Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness cache
  rw [hsampleRun]
  rw [Concrete.signingRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey leafIndex message randomness :
            OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))
  rw [hroute]

end XmssSecurity.Checksum

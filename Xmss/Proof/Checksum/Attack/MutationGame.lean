import Xmss.Proof.Checksum.Attack.MutationAverage
import Xmss.Proof.Common.Modes.Direct
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-! Relating the mutation experiment to the adversary's logged security game. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.Checksum.Attack

open Hashing Wots Merkle Verify Keygen Signing

def worldPrivateSamples {α : Type} (computation : ProbComp α) : OracleComp OracleWorld α :=
  simulateQ (fun input => liftM (OracleWorld.query (.inl input))) computation

theorem liftPrivateSamples_logged {Key α : Type} (scheme : Scheme Key) (secretKey : Key)
    (computation : ProbComp α) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey)
      (Attack.liftPrivateSamples computation)).run =
      (fun value => (value, [])) <$> worldPrivateSamples computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Attack.liftPrivateSamples, worldPrivateSamples]
  | query_bind input next ih =>
      simp only [Attack.liftPrivateSamples, worldPrivateSamples, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      simp only [QueryImpl.add_apply_inl, forwardOracles, WriterT.run_bind]
      have hquery : (liftM (OracleWorld.query (.inl input)) :
          WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (unifSpec.Range input)).run =
          (fun value => (value, [])) <$> (liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _) := rfl
      rw [hquery]
      simp only [bind_map_left, ih, map_bind, Functor.map_map, List.nil_append]
      rfl

theorem worldPrivateSamples_run {α : Type} (computation : ProbComp α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (worldPrivateSamples computation)).run cache =
      (fun value => (value, cache)) <$> computation := by
  unfold worldPrivateSamples
  rw [← QueryImpl.simulateQ_compose]
  have hcompose : romImpl ∘ₛ (fun input => liftM (OracleWorld.query (.inl input))) =
      unifFwdImpl HashSpec := by
    funext input
    simp only [QueryImpl.apply_compose, simulateQ_spec_query, romImpl, QueryImpl.add_apply_inl]
  rw [hcompose]
  exact unifFwdImpl.simulateQ_run computation cache

theorem oneRequestSamples_logged {Key α β : Type} (scheme : Scheme Key) (secretKey : Key)
    (request : SignRequest) (samples : ProbComp β) (finish : Option Generic.Signature → β → α) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey) (do
      let answer ← liftM ((OracleWorld + SigningSpec).query (.inr request))
      let choice ← Attack.liftPrivateSamples samples
      pure (finish answer choice))).run = (do
      let answer ← scheme.sign secretKey request.epoch request.message
      let choice ← worldPrivateSamples samples
      return (finish answer choice, [⟨request, answer⟩])) := by
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  have hsign : (signingOracle scheme secretKey request).run =
      (scheme.sign secretKey request.epoch request.message >>= fun answer =>
        pure (answer, [⟨request, answer⟩])) :=
    QueryImpl.run_withLogging_apply _ _
  simp only [QueryImpl.add_apply_inr, hsign, bind_map_left, simulateQ_map,
    WriterT.run_map', liftPrivateSamples_logged, bind_pure_comp, Functor.map_map,
    Prod.map_apply, id_eq, List.append_nil]

theorem chainMutationMain_logged {Key : Type} (scheme : Scheme Key) (secretKey : Key) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey) Attack.chainMutationMain).run = (do
      let answer ← scheme.sign secretKey Attack.mutationRequest.epoch Attack.mutationRequest.message
      let choice ← worldPrivateSamples Attack.mutationChoice
      return (Attack.chainMutationForgery answer choice, [⟨Attack.mutationRequest, answer⟩])) :=
  oneRequestSamples_logged scheme secretKey Attack.mutationRequest Attack.mutationChoice Attack.chainMutationForgery

theorem chainMutation_gameRest {Key : Type} (scheme : Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    Seeded.gameRest scheme Attack.chainMutationAdversary publicKey secretKey = (do
      let answer ← scheme.sign secretKey Attack.mutationRequest.epoch Attack.mutationRequest.message
      let choice ← worldPrivateSamples Attack.mutationChoice
      let forgery := Attack.chainMutationForgery answer choice
      let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
      return decide (SigningTranscript.Valid [⟨Attack.mutationRequest, answer⟩] ∧
        ¬SigningTranscript.Contains [⟨Attack.mutationRequest, answer⟩] forgery) && verified) := by
  unfold Seeded.gameRest
  change (do
    let result ← (simulateQ (forwardOracles + signingOracle scheme secretKey) Attack.chainMutationMain).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified) = _
  rw [chainMutationMain_logged]
  simp only [bind_assoc, pure_bind]

def mutationOutcome (publicKey : PublicKey) (answer : Option Generic.Signature) (choice : Generic.ChainIndex × Digest) :
    OracleComp HashSpec Bool := do
  let forgery := Attack.chainMutationForgery answer choice
  let verified ← Generic.Verify.verify publicKey forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid [⟨Attack.mutationRequest, answer⟩] ∧
    ¬SigningTranscript.Contains [⟨Attack.mutationRequest, answer⟩] forgery) && verified

theorem chainMutation_referenceRest_run (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (Seeded.gameRest precomputedScheme Attack.chainMutationAdversary publicKey secretKey)).run cache = (do
      let result ← (simulateQ romImpl
        (Signing.precomputedCappedSign secretKey Attack.mutationRequest.epoch Attack.mutationRequest.message)).run cache
      let choice ← Attack.mutationChoice
      (simulateQ randomOracle (mutationOutcome publicKey result.1 choice)).run result.2) := by
  rw [chainMutation_gameRest, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨answer, signCache⟩
  rw [simulateQ_bind, StateT.run_bind, worldPrivateSamples_run, bind_map_left]
  apply bind_congr
  intro choice
  have hroute : simulateQ romImpl
      (liftM (Generic.Verify.verify publicKey (Attack.chainMutationForgery answer choice).epoch
        (Attack.chainMutationForgery answer choice).message (Attack.chainMutationForgery answer choice).signature :
          OracleComp HashSpec Bool)) =
      simulateQ randomOracle (Generic.Verify.verify publicKey (Attack.chainMutationForgery answer choice).epoch
        (Attack.chainMutationForgery answer choice).message (Attack.chainMutationForgery answer choice).signature :
          OracleComp HashSpec Bool) :=
    QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _
  unfold mutationOutcome
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  change (simulateQ romImpl (liftM (Generic.Verify.verify publicKey (Attack.chainMutationForgery answer choice).epoch
      (Attack.chainMutationForgery answer choice).message (Attack.chainMutationForgery answer choice).signature :
        OracleComp HashSpec Bool))).run signCache >>= _ = _
  rw [hroute]
  simp only [simulateQ_pure, StateT.run_pure]

local instance : Nonempty Generic.ChainIndex := ⟨⟨0, Code.numChains_pos⟩⟩
noncomputable local instance : SampleableType Generic.ChainIndex := SampleableType.ofFintype Generic.ChainIndex

theorem evalDist_bind_mutationChoice {α : Type} (next : Generic.ChainIndex × Digest → ProbComp α) :
    evalDist (Attack.mutationChoice >>= next) = evalDist (do
      let chain ← $ᵗ Generic.ChainIndex
      let value ← $ᵗ Digest
      next (chain, value)) := by
  have hchoice : evalDist Attack.mutationChoice = evalDist (do
      let chain ← $ᵗ Generic.ChainIndex
      let value ← $ᵗ Digest
      pure (chain, value)) := by
    calc
      _ = evalDist ($ᵗ (Generic.ChainIndex × Digest)) := by
        rw [Attack.mutationChoice_evalDist, evalDist_uniformSample]
      _ = _ := evalDist_independent_uniform_pair.symm
  rw [evalDist_bind, hchoice, ← evalDist_bind]
  congr 1

theorem mutationOutcome_some (publicKey : PublicKey) (signature : Generic.Signature) (choice : Generic.ChainIndex × Digest) :
    mutationOutcome publicKey (some signature) choice = (do
      let verified ← (Generic.Verify.verify publicKey Attack.mutationRequest.epoch Attack.mutationRequest.message
        (CappedExecution.replaceSignatureChainValue signature choice.1 choice.2) : OracleComp HashSpec Bool)
      return decide (choice.2 ≠ signature.chainValue choice.1) && verified) := by
  have hcontains : SigningTranscript.Contains [⟨Attack.mutationRequest, some signature⟩]
      (Attack.chainMutationForgery (some signature) choice) ↔
      signature = (Attack.chainMutationForgery (some signature) choice).signature := by
    simp [Unforgeability.SigningTranscript.Contains, Attack.chainMutationForgery, Unforgeability.Forgery.request]
  have hfresh : ¬SigningTranscript.Contains [⟨Attack.mutationRequest, some signature⟩]
      (Attack.chainMutationForgery (some signature) choice) ↔ choice.2 ≠ signature.chainValue choice.1 := by
    rw [hcontains]
    exact ne_comm.trans (Attack.chainMutationForgery_distinct_iff signature choice)
  unfold mutationOutcome
  simp only [Attack.chainMutation_transcript_valid, true_and, hfresh]
  rfl

noncomputable def mutationOutcomeRun (publicKey : PublicKey) (answer : Option Generic.Signature)
    (cache : QueryCache HashSpec) : ProbComp (Bool × QueryCache HashSpec) := do
  let choice ← Attack.mutationChoice
  (simulateQ randomOracle (mutationOutcome publicKey answer choice)).run cache

theorem mutationOutcomeRun_some_probability (publicKey : PublicKey) (signature : Generic.Signature)
    (cache : QueryCache HashSpec) :
    Pr[fun result => result.1 = true | mutationOutcomeRun publicKey (some signature) cache] =
      Pr[= true | uniformChainVerification publicKey Attack.mutationRequest signature cache] := by
  unfold mutationOutcomeRun
  rw [probEvent_def, evalDist_bind_mutationChoice, ← probEvent_def]
  unfold uniformChainVerification Attack.randomMutationVerification
  rw [← probEvent_eq_eq_probOutput]
  simp only [mutationOutcome_some, bind_pure_comp, simulateQ_map, StateT.run_map,
    probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Bool.and_eq_true, decide_eq_true_eq]

theorem signedMutationExperiment_le_referenceRest
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) :
    Pr[= true | signedMutationExperiment keyResult Attack.mutationRequest] ≤
      Pr[fun result => result.1 = true |
        (simulateQ romImpl (Seeded.gameRest precomputedScheme Attack.chainMutationAdversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2] := by
  unfold signedMutationExperiment
  rw [probOutput_bind_eq_tsum, chainMutation_referenceRest_run, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  rintro ⟨answer, finalCache⟩
  cases answer with
  | none => simp
  | some signature =>
      change _ ≤ _ * Pr[fun result => result.1 = true |
        mutationOutcomeRun keyResult.1.1 (some signature) finalCache]
      rw [mutationOutcomeRun_some_probability]

theorem chainMutation_referenceRest_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)) :
    (127 / 128 : ℝ≥0∞) * ((1165 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains) ≤
      Pr[fun result => result.1 = true |
        (simulateQ romImpl (Seeded.gameRest precomputedScheme Attack.chainMutationAdversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2] :=
  (signedMutationExperiment_probability_lower keyResult hkey Attack.mutationRequest).trans
    (signedMutationExperiment_le_referenceRest keyResult)

theorem chainMutation_reference_advantage_lower :
    (127 / 128 : ℝ≥0∞) * ((1165 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains) ≤
      forgeAdvantage precomputedScheme Attack.chainMutationAdversary := by
  let lower : ℝ≥0∞ := (127 / 128) * ((1165 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains)
  let keys := (simulateQ romImpl precomputedScheme.keygen).run ∅
  have hmass : ∑' keyResult, Pr[= keyResult | keys] = 1 := tsum_probOutput_eq_one' (by simp)
  rw [forgeAdvantage_eq_gameWithCache]
  unfold gameWithCache gameCore
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    _ = ∑' keyResult, Pr[= keyResult | keys] * lower := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support keys
      · exact mul_le_mul_right (chainMutation_referenceRest_lower keyResult hkey) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hkey
        change _ ≤ Pr[= keyResult | keys] * _
        rw [hzero]
        simp

theorem chainMutation_reference_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      forgeAdvantage precomputedScheme Attack.chainMutationAdversary := by
  apply lt_of_lt_of_le _ chainMutation_reference_advantage_lower
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by
    apply ENNReal.mul_ne_top
    · finiteness
    · exact ENNReal.div_ne_top (by finiteness) (by norm_num [numChains]))).mp
  norm_num [digestBits, numChains, ENNReal.toReal_mul, ENNReal.toReal_div]

/-- info: 'Xmss.Checksum.Attack.chainMutation_reference_advantage_exceeds_123' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_reference_advantage_exceeds_123

end Xmss.Checksum.Attack

import Xmss.Proof.TargetSum.Attack.NeighborAdversary
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.CacheDecode
import Xmss.Proof.TargetSum.EncodingProbability

/-! The neighboring-signature experiment is a lower bound for the concrete adversary's game. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.Attack

open Hashing Wots Merkle Verify Keygen Signing

theorem liftWorldToAdversary_logged {Key α : Type} (scheme : Scheme Key) (secretKey : Key)
    (computation : OracleComp OracleWorld α) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey)
      (liftWorldToAdversary computation)).run = (fun value => (value, [])) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftWorldToAdversary]
  | query_bind input next ih =>
      simp only [liftWorldToAdversary, simulateQ_bind, simulateQ_spec_query] at ih ⊢
      simp only [QueryImpl.add_apply_inl, forwardOracles, WriterT.run_bind]
      have hquery : (liftM (OracleWorld.query input) :
          WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (OracleWorld.Range input)).run =
          (fun value => (value, [])) <$> (liftM (OracleWorld.query input) : OracleComp OracleWorld _) := rfl
      rw [hquery]
      simp only [bind_map_left, ih, map_bind, Functor.map_map, List.nil_append]

theorem neighborMain_logged {Key : Type} (scheme : Scheme Key) (secretKey : Key) (publicKey : PublicKey) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey) (neighborMain publicKey)).run = (do
      let answer ← scheme.sign secretKey neighborRequest.epoch neighborRequest.message
      let signature ← neighborAfterSigning publicKey answer
      return (neighborForgery signature, [⟨neighborRequest, answer⟩])) := by
  unfold neighborMain
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  have hsign : (signingOracle scheme secretKey neighborRequest).run =
      (scheme.sign secretKey neighborRequest.epoch neighborRequest.message >>= fun answer =>
        pure (answer, [⟨neighborRequest, answer⟩])) := QueryImpl.run_withLogging_apply _ _
  simp only [QueryImpl.add_apply_inr, hsign, bind_map_left, simulateQ_map,
    WriterT.run_map', liftWorldToAdversary_logged, bind_pure_comp, Functor.map_map,
    Prod.map_apply, id_eq, List.append_nil]

theorem neighbor_transcript_fresh (answer : Option Generic.Signature) (signature : Generic.Signature) :
    ¬SigningTranscript.Contains [⟨neighborRequest, answer⟩] (neighborForgery signature) := by
  simp only [Unforgeability.SigningTranscript.Contains, List.mem_singleton, exists_eq_left, not_and]
  intro heq _
  exact neighborMessage_ne_request (congrArg (fun request : SignRequest => request.message) heq).symm

theorem neighbor_gameRest {Key : Type} (scheme : Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    Seeded.gameRest scheme neighborAdversary publicKey secretKey = (do
      let answer ← scheme.sign secretKey neighborRequest.epoch neighborRequest.message
      let signature ← neighborAfterSigning publicKey answer
      scheme.verify publicKey neighborRequest.epoch neighborMessage signature) := by
  unfold Seeded.gameRest
  change (do
    let result ← (simulateQ (forwardOracles + signingOracle scheme secretKey) (neighborMain publicKey)).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified) = _
  rw [neighborMain_logged]
  simp only [bind_assoc, pure_bind, neighbor_transcript_fresh, not_false_eq_true, and_true,
    show ∀ answer : Option Generic.Signature, SigningTranscript.Valid [⟨neighborRequest, answer⟩] from
      fun _ => by simp [Unforgeability.SigningTranscript.Valid], decide_true, Bool.true_and, bind_pure]
  rfl

theorem hash_run'_bind {α β : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp HashSpec β) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (computation >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ randomOracle (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

theorem world_run'_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (computation >>= next)).run' cache =
      ((simulateQ romImpl computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

theorem simulateQ_rom_liftHash {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ romImpl (liftM computation : OracleComp OracleWorld α) = simulateQ randomOracle computation :=
  QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _

theorem neighborFinish_probability_ge_predecessor (publicKey : PublicKey) (original : Generic.Signature)
    (encoding : Encoding) (randomness : Randomness) (transfer : DigitTransfer encoding) (cache : QueryCache HashSpec) :
    Pr[= true | predecessorVerificationExperiment publicKey neighborRequest.epoch neighborMessage original encoding
      randomness transfer cache] ≤
      Pr[= true | (do
        let block ← $ᵗ PreimagePrefix
        (simulateQ randomOracle (do
          let signature ← neighborFinish publicKey original encoding randomness transfer block
          Generic.Verify.verify publicKey neighborRequest.epoch neighborMessage signature)).run' cache)] := by
  unfold predecessorVerificationExperiment randomDigestPreimage
  simp only [bind_assoc, pure_bind]
  apply probOutput_bind_mono
  intro block _
  rw [neighborFinish, bind_assoc, hash_run'_bind]
  apply probOutput_bind_mono
  rintro ⟨answer, searchCache⟩ _
  cases answer with
  | none => simp [checkNeighborPreimage]
  | some answer =>
      rcases answer with ⟨position, output⟩
      simp only [checkNeighborPreimage, bind_pure_comp, bind_map_left, StateT.run'_eq]
      exact le_rfl

theorem neighborAfterEncoding_probability_ge_experiment (publicKey : PublicKey) (original : Generic.Signature)
    (encoding : Encoding) (cache : QueryCache HashSpec) :
    Pr[= true | neighborVerificationExperiment publicKey neighborRequest.epoch neighborMessage original encoding cache] ≤
      Pr[= true | (simulateQ romImpl (do
        let signature ← neighborAfterEncoding publicKey original encoding
        liftM (Generic.Verify.verify publicKey neighborRequest.epoch neighborMessage signature : OracleComp HashSpec Bool))).run' cache] := by
  classical
  unfold neighborVerificationExperiment neighborAfterEncoding
  rw [bind_assoc, world_run'_bind, simulateQ_rom_liftHash]
  apply probOutput_bind_mono
  rintro ⟨answer, searchCache⟩ _
  cases answer with
  | none => simp [neighborVerificationContinuation]
  | some answer =>
      rcases answer with ⟨position, output⟩
      by_cases hmem : output ∈ neighborDigests encoding
      · simp only [neighborVerificationContinuation, dif_pos hmem, bind_assoc]
        rw [world_run'_bind, worldPrivateSamples_run, bind_map_left]
        have heq : (do
            let block ← $ᵗ PreimagePrefix
            (simulateQ romImpl (do
              let signature ← liftM (neighborFinish publicKey original encoding (BitVec.ofNat digestBits position)
                (selectedNeighborTransfer encoding (output) hmem) block)
              liftM (Generic.Verify.verify publicKey neighborRequest.epoch neighborMessage signature : OracleComp HashSpec Bool))).run' searchCache) =
            (do
              let block ← $ᵗ PreimagePrefix
              (simulateQ randomOracle (do
                let signature ← neighborFinish publicKey original encoding (BitVec.ofNat digestBits position)
                  (selectedNeighborTransfer encoding (output) hmem) block
                Generic.Verify.verify publicKey neighborRequest.epoch neighborMessage signature)).run' searchCache) := by
          apply bind_congr
          intro block
          rw [world_run'_bind, simulateQ_rom_liftHash, hash_run'_bind]
          apply bind_congr
          intro result
          rw [simulateQ_rom_liftHash]
        rw [heq]
        exact neighborFinish_probability_ge_predecessor _ _ _ _ _ _
      · simp [neighborVerificationContinuation, hmem]

theorem neighborAfterSigning_probability_ge_experiment (publicKey : PublicKey) (original : Generic.Signature)
    (encoding : Encoding) (cache : QueryCache HashSpec)
    (hdecode : Code.decodeDigest (CacheView.encodingHash cache publicKey.parameter
      neighborRequest.epoch (neighborRequest.message, original.randomness)) = some encoding) :
    Pr[= true | neighborVerificationExperiment publicKey neighborRequest.epoch neighborMessage original encoding cache] ≤
      Pr[= true | (simulateQ romImpl (do
        let signature ← neighborAfterSigning publicKey (some original)
        liftM (Generic.Verify.verify publicKey neighborRequest.epoch neighborMessage signature : OracleComp HashSpec Bool))).run' cache] := by
  rw [neighborAfterSigning, bind_assoc, world_run'_bind, simulateQ_rom_liftHash,
    Attack.encodingHash_run_cached _ _ _ _ _ _
      (TargetSum.decodedEncoding_of_decodeDigest hdecode), pure_bind, hdecode]
  exact neighborAfterEncoding_probability_ge_experiment _ _ _ _

theorem signedNeighborExperiment_le_referenceRest
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)) :
    Pr[= true | signedNeighborExperiment keyResult neighborRequest neighborMessage] ≤
      Pr[= true | (simulateQ romImpl
        (Seeded.gameRest precomputedScheme neighborAdversary keyResult.1.1 keyResult.1.2)).run' keyResult.2] := by
  unfold signedNeighborExperiment
  rw [neighbor_gameRest, world_run'_bind]
  apply probOutput_bind_mono
  rintro ⟨answer, signCache⟩ hsign
  cases answer with
  | none => simp
  | some original =>
      obtain ⟨encoding, hdecoded, _⟩ := Attack.signing_success_replay_at_keygen keyResult hkey neighborRequest original signCache hsign
      have hdecode := CacheView.decodeDigest_of_decodedEncoding hdecoded
      simp only [hdecode]
      exact neighborAfterSigning_probability_ge_experiment keyResult.1.1 original encoding signCache
        (by rw [Deciding.keygen_publicKey_parameter_eq keyResult hkey]; exact hdecode)

theorem neighbor_referenceRest_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)) :
    (31 / 32 : ℝ≥0∞) * ((5 / 6) * (2 / 5)) ≤
      Pr[= true | (simulateQ romImpl
        (Seeded.gameRest precomputedScheme neighborAdversary keyResult.1.1 keyResult.1.2)).run' keyResult.2] :=
  (signedNeighborExperiment_lower keyResult hkey neighborRequest neighborMessage neighborMessage_ne_request).trans
    (signedNeighborExperiment_le_referenceRest keyResult hkey)

theorem neighbor_reference_advantage_lower :
    (31 / 32 : ℝ≥0∞) * ((5 / 6) * (2 / 5)) ≤ forgeAdvantage precomputedScheme neighborAdversary := by
  let lower : ℝ≥0∞ := (31 / 32) * ((5 / 6) * (2 / 5))
  let keys := (simulateQ romImpl precomputedScheme.keygen).run ∅
  have hmass : ∑' keyResult, Pr[= keyResult | keys] = 1 := tsum_probOutput_eq_one' (by simp)
  unfold forgeAdvantage gameCore
  rw [world_run'_bind, probOutput_bind_eq_tsum]
  calc
    _ = ∑' keyResult, Pr[= keyResult | keys] * lower := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support keys
      · exact mul_le_mul_right (neighbor_referenceRest_lower keyResult hkey) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hkey
        change _ ≤ Pr[= keyResult | keys] * _
        rw [hzero]
        simp

theorem neighbor_reference_advantage_exceeds_nine_thirtyseconds :
    9 / 32 < forgeAdvantage precomputedScheme neighborAdversary := by
  apply lt_of_lt_of_le _ neighbor_reference_advantage_lower
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- info: 'Xmss.TargetSum.Attack.neighborAfterEncoding_probability_ge_experiment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborAfterEncoding_probability_ge_experiment

/-- info: 'Xmss.TargetSum.Attack.neighbor_reference_advantage_exceeds_nine_thirtyseconds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighbor_reference_advantage_exceeds_nine_thirtyseconds

end Xmss.TargetSum.Attack

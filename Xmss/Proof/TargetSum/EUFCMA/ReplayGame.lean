import Xmss.Proof.TargetSum.EUFCMA.ReplayAdversary
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The logged standard game realizes the replay/fallback reference experiment. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing Attack

theorem replayAfterSigning_verification_eq (publicKey : PublicKey) (original : Generic.Signature)
    (cache : QueryCache HashSpec) :
    (simulateQ Generic.romImpl (do
      let forgery ← replayAfterSigning publicKey (some original)
      Generic.precomputedScheme.verify publicKey forgery.epoch forgery.message forgery.signature)).run' cache =
      replayFallbackExperiment publicKey replayRequest.epoch replayCandidate replayFallbackMessage original cache := by
  unfold replayAfterSigning replayFallbackExperiment
  simp only [Option.getD_some, bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query,
    StateT.run'_bind']
  apply bind_congr
  rintro ⟨output, finalCache⟩
  rw [show Generic.precomputedScheme.verify publicKey replayRequest.epoch (replaySelectedMessage output) original =
    liftM (Generic.Verify.verify publicKey replayRequest.epoch (replaySelectedMessage output) original :
      OracleComp HashSpec Bool) from rfl, simulateQ_rom_liftHash]
  rfl

theorem signedReplayFallbackExperiment_le_gameRest
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) :
    Pr[= true | signedReplayFallbackExperiment keyResult replayRequest replayCandidate replayFallbackMessage] ≤
      Pr[= true | (simulateQ Generic.romImpl
        (gameRest Generic.precomputedScheme replayAdversary keyResult.1.1 keyResult.1.2)).run' keyResult.2] := by
  unfold signedReplayFallbackExperiment
  rw [replay_gameRest, world_run'_bind]
  apply probOutput_bind_mono
  rintro ⟨answer, signCache⟩ _
  cases answer with
  | none => simp
  | some original => rw [replayAfterSigning_verification_eq]

theorem replay_reference_advantage_lower :
    (131071 / 131072 : ℝ≥0∞) * replayFallbackRate ≤ forgeAdvantage Generic.precomputedScheme replayAdversary := by
  let lower : ℝ≥0∞ := (131071 / 131072) * replayFallbackRate
  let keys := (simulateQ Generic.romImpl Generic.precomputedScheme.keygen).run ∅
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
      · exact mul_le_mul' le_rfl ((signedReplayFallbackExperiment_lower keyResult hkey replayRequest
          replayCandidate replayFallbackMessage (by decide) (by decide) (by decide)).trans
            (signedReplayFallbackExperiment_le_gameRest keyResult))
      · have hzero := probOutput_eq_zero_of_not_mem_support hkey
        change _ ≤ Pr[= keyResult | keys] * _
        rw [hzero]
        simp

theorem replay_reference_advantage_exceeds_127 :
    ((2 ^ 127 : ℕ) : ℝ≥0∞)⁻¹ < forgeAdvantage Generic.precomputedScheme replayAdversary :=
  signedReplayFallbackRate_gt_127.trans_le replay_reference_advantage_lower

theorem replay_advantage_eq_strong {Key : Type} (scheme : Generic.Scheme Key) :
    forgeAdvantage scheme replayAdversary = Generic.forgeAdvantage scheme replayAdversary := by
  unfold forgeAdvantage Generic.forgeAdvantage gameCore Generic.gameCore
  congr 3
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  exact (replay_strong_gameRest scheme publicKey secretKey).symm

/-- info: 'Xmss.TargetSum.EUFCMA.replay_reference_advantage_exceeds_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_reference_advantage_exceeds_127

end Xmss.TargetSum.EUFCMA

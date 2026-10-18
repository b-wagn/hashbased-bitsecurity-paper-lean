import XmssSecurity.Proof.TargetSum.EUFCMA.ReferenceHop
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Refine the standard-unforgeability seed hop using the expected number of
seed-domain queries instead of the worst-case direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded XmssSecurity.TargetSum.Seeded

noncomputable def expectedTableSeedQueries (adversary : Generic.Adversary) : ℝ≥0∞ :=
  ∑' material, Pr[= material | Generic.Seeded.drawSigningMaterial] *
    expectedSimulatedQueryCount Generic.romImpl (Generic.Seeded.hashBad Generic.MaySeedHit)
      (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2) ∅

theorem forgeAdvantage_deterministic_le_table_expectedSeed (adversary : Generic.Adversary) :
    forgeAdvantage Generic.Seeded.scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      expectedTableSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | Generic.Seeded.drawSigningMaterial >>= fun material => Generic.sampleMasterSeed >>= fun seed =>
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run'
        (Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | Generic.Seeded.drawSigningMaterial >>= fun material =>
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run' ∅] + _
  simp only [probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' material, Pr[= material | Generic.Seeded.drawSigningMaterial] *
        (Pr[= true | (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1)
            (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run' ∅] +
          expectedSimulatedQueryCount Generic.romImpl (Generic.Seeded.hashBad Generic.MaySeedHit)
            (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1)
              material.2.2) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro material
      apply mul_le_mul' le_rfl
      have h := probEvent_random_cache_change_derivationHit_le_expected
        (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2)
        (fun seed => Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
        (fun seed => Generic.Seeded.signingDerivationCache_agreeOutside_derivationHit seed _ _ _) (fun value => value = true)
      simpa only [probEvent_eq_eq_probOutput, probOutput_bind_eq_tsum] using h
    _ = _ := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_table_expectedSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_table_expectedSeed

end XmssSecurity.TargetSum.EUFCMA.Seeded

import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Seeded.ExpectedHashTrace
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Seed guessing is charged to the expected number of seed-derivation-tag queries,
with no charge for encoding, chain, or Merkle queries. The refinement does not require
a syntactic query bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Seeded

open scoped Classical in
theorem probOutput_stopBefore_derivationHit_le_expected {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | Generic.sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (Seeded.stopBefore (Seeded.hashBad (Seeded.DerivationHit seed)) computation)).run' cache] ≤
      expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit) computation cache /
        ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let trace := (simulateQ romImpl (Seeded.traceHashes computation)).run' cache
  calc
    _ = Pr[= true | Generic.sampleMasterSeed >>= fun seed =>
        (fun result => decide (Seeded.TraceHits (Seeded.DerivationHit seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, Seeded.probOutput_stopBefore_none, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (Seeded.TraceHits (Seeded.DerivationHit seed) result.2)) <$> Generic.sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ ∑' result, Pr[= result | trace] *
        (((result.2.filter (fun input => decide (MaySeedHit input))).length : ℝ≥0∞) /
          ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
      rw [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      simpa only [probEvent_map, Function.comp_def, decide_eq_true_eq] using
        Seeded.probEvent_traceHits_derivationHit_le result.2
    _ = _ := by
      rw [expectedHashQueries_eq_filtered_trace]
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]

open scoped Classical in
theorem probEvent_random_cache_change_derivationHit_le_expected {α : Type}
    (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, Seeded.AgreeOutside (Seeded.DerivationHit seed) (initial seed) cache) (event : α → Prop) :
    Pr[event | Generic.sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] +
        expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit) computation cache /
          ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let stopped := fun seed =>
    (simulateQ romImpl (Seeded.stopBefore (Seeded.hashBad (Seeded.DerivationHit seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | Generic.sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | Generic.sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (Seeded.probEvent_cache_change_le (Seeded.DerivationHit seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (probOutput_stopBefore_derivationHit_le_expected computation cache)

noncomputable def expectedTableSeedQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' material, Pr[= material | Seeded.drawSigningMaterial] *
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
      (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Seeded.outputSecrets material.2.1) material.2.2) ∅

theorem forgeAdvantage_deterministic_le_table_expectedSeed (adversary : Adversary) :
    forgeAdvantage Seeded.scheme adversary ≤ Pr[= true | Seeded.independentTableGame adversary] +
      expectedTableSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage Seeded.independentTableGame
  simp only [probOutput_def, Seeded.evalDist_gameCore_deterministic_programmed,
    Seeded.evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | Seeded.drawSigningMaterial >>= fun material => Generic.sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Seeded.outputSecrets material.2.1) material.2.2)).run'
        (Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | Seeded.drawSigningMaterial >>= fun material =>
      (simulateQ romImpl (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Seeded.outputSecrets material.2.1) material.2.2)).run' ∅] + _
  simp only [probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' material, Pr[= material | Seeded.drawSigningMaterial] *
        (Pr[= true | (simulateQ romImpl (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1)
            (Seeded.outputSecrets material.2.1) material.2.2)).run' ∅] +
          expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
            (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Seeded.outputSecrets material.2.1)
              material.2.2) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro material
      apply mul_le_mul' le_rfl
      have h := probEvent_random_cache_change_derivationHit_le_expected
        (Seeded.tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Seeded.outputSecrets material.2.1) material.2.2)
        (fun seed => Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
        (fun seed => Seeded.signingDerivationCache_agreeOutside_derivationHit seed _ _ _) (fun value => value = true)
      simpa only [probEvent_eq_eq_probOutput, probOutput_bind_eq_tsum] using h
    _ = _ := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rfl

end XmssSecurity.TargetSum.Seeded

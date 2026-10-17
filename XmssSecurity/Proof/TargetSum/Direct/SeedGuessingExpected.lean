import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Seeded.ExpectedHashTrace

/-! Seed guessing is charged to the expected number of seed-derivation-tag queries,
with no charge for encoding, chain, or Merkle queries. The refinement does not require
a syntactic query bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

open scoped Classical in
theorem probOutput_stopBefore_derivationHit_le_expected {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (stopBefore (hashBad (DerivationHit seed)) computation)).run' cache] ≤
      expectedSimulatedQueryCount romImpl (hashBad MaySeedHit) computation cache /
        ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceHits (DerivationHit seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (TraceHits (DerivationHit seed) result.2)) <$> sampleMasterSeed] := by
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
        probEvent_traceHits_derivationHit_le result.2
    _ = _ := by
      rw [expectedHashQueries_eq_filtered_trace]
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]

open scoped Classical in
theorem probEvent_random_cache_change_derivationHit_le_expected {α : Type}
    (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (DerivationHit seed) (initial seed) cache) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] +
        expectedSimulatedQueryCount romImpl (hashBad MaySeedHit) computation cache /
          ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (DerivationHit seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (DerivationHit seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (probOutput_stopBefore_derivationHit_le_expected computation cache)

noncomputable def expectedTableSeedQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' material, Pr[= material | drawSigningMaterial] *
    expectedSimulatedQueryCount romImpl (hashBad MaySeedHit)
      (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2) ∅

theorem forgeAdvantage_deterministic_le_table_expectedSeed (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      expectedTableSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | drawSigningMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | drawSigningMaterial >>= fun material =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run' ∅] + _
  simp only [probOutput_bind_eq_tsum]
  calc
    _ ≤ ∑' material, Pr[= material | drawSigningMaterial] *
        (Pr[= true | (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
            (outputSecrets material.2.1) material.2.2)).run' ∅] +
          expectedSimulatedQueryCount romImpl (hashBad MaySeedHit)
            (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1)
              material.2.2) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro material
      apply mul_le_mul' le_rfl
      have h := probEvent_random_cache_change_derivationHit_le_expected
        (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)
        (fun seed => signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
        (fun seed => signingDerivationCache_agreeOutside_derivationHit seed _ _ _) (fun value => value = true)
      simpa only [probEvent_eq_eq_probOutput, probOutput_bind_eq_tsum] using h
    _ = _ := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rfl

theorem forgeAdvantage_deterministic_le_reference_expectedSeed (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      expectedTableSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table_expectedSeed adversary).trans (add_le_add hmemo le_rfl)

theorem expectedTableSeedQueries_le (adversary : Adversary) (D : Nat)
    (hD : Direct.IsDirectQueryBound adversary D) : expectedTableSeedQueries adversary ≤ D := by
  unfold expectedTableSeedQueries
  calc
    _ ≤ ∑' material, Pr[= material | drawSigningMaterial] * (D : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro material
      exact mul_le_mul' le_rfl (expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ ∅ D
        (tableGameAfterSecrets_bound adversary D hD _ _ _))
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

/-- info: 'XmssSecurity.TargetSum.Seeded.forgeAdvantage_deterministic_le_reference_expectedSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedSeed

end XmssSecurity.TargetSum.Seeded

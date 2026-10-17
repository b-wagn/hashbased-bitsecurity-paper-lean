import XmssSecurity.Proof.TargetSum.Modes.SignerReferenceBudget
import XmssSecurity.Proof.TargetSum.Deterministic.PhaseCounts

/-! The reference phase shares one budget between direct hashes and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded DeterministicSigning

theorem signer_referencePhaseCounts_bound
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.TargetSum.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × PhaseCounts)
    (hresult : result ∈ support ((simulateQ (referencePhaseCountsImpl keyResult.1.2)
      (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run
        ⟨keyResult.2, 0, 0⟩)) :
    result.2.direct + 2 * result.2.signing ≤ q := by
  apply signer_referencePhaseCost_le_after_keygen adversary q hsmall hbound keyResult hkey
    (result.1, result.2.weighted 2)
  have hproject := referencePhaseCounts_cost_projection keyResult.1.2
    (withRequestLog (memoize (adversary.main keyResult.1.1) ∅)) ⟨keyResult.2, 0, 0⟩
  simp only [PhaseCounts.weighted, Nat.mul_zero, Nat.zero_add] at hproject
  rw [← hproject, support_map]
  exact ⟨result, hresult, rfl⟩

theorem reference_runWorldSigning_eq_adversaryPhase
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : XmssSecurity.TargetSum.SecretKey) :
    runWorldSigning
      (fun request => Concrete.precomputedCappedSign secretKey request.epoch request.message)
      (withRequestLog (adversary.main publicKey)) =
        Deciding.adversaryPhase adversary publicKey secretKey := by
  rw [runWorldSigning_withRequestLog]
  rfl

theorem signer_reference_adversaryPhase_hashQueryBound
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.TargetSum.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    HashQueryBound (Deciding.adversaryPhase (memoAdversary (Security.embed adversary))
      keyResult.1.1 keyResult.1.2) keyResult.2 q := by
  rw [hashQueryBound_iff_costState, ← reference_runWorldSigning_eq_adversaryPhase]
  intro result hresult
  have hproject := phaseCounts_fullHashCount_projection
    (fun (request : SignRequest) =>
      Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)
    (withRequestLog ((memoAdversary (Security.embed adversary)).main keyResult.1.1))
      ⟨keyResult.2, 0, 0⟩
  dsimp only at hproject
  rw [← hproject, support_map] at hresult
  obtain ⟨counts, hcounts, rfl⟩ := hresult
  have h := signer_referencePhaseCounts_bound adversary q hsmall hbound keyResult hkey counts hcounts
  dsimp only
  omega

theorem signer_expected_reference_adversaryPhase_hashQueries_le
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.TargetSum.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    expectedSimulatedQueryCount romImpl IsHashQuery
      (Deciding.adversaryPhase (memoAdversary (Security.embed adversary))
        keyResult.1.1 keyResult.1.2) keyResult.2 ≤ q :=
  expectedHashQueries_le_of_hashQueryBound _ _ _
    (signer_reference_adversaryPhase_hashQueryBound adversary q hsmall hbound keyResult hkey)

theorem signer_referencePhaseCounts_expected_bound
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.TargetSum.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    let phase := (simulateQ (referencePhaseCountsImpl keyResult.1.2)
      (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run
        ⟨keyResult.2, 0, 0⟩
    (∑' result, Pr[= result | phase] * (result.2.direct : ℝ≥0∞)) +
      2 * (∑' result, Pr[= result | phase] * (result.2.signing : ℝ≥0∞)) ≤ q := by
  dsimp only
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ (referencePhaseCountsImpl keyResult.1.2)
        (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run
          ⟨keyResult.2, 0, 0⟩] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [mul_left_comm 2, ← mul_add]
      by_cases hresult : result ∈ support ((simulateQ (referencePhaseCountsImpl keyResult.1.2)
          (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run
            ⟨keyResult.2, 0, 0⟩)
      · apply mul_le_mul' le_rfl
        exact_mod_cast signer_referencePhaseCounts_bound adversary q hsmall hbound
          keyResult hkey result hresult
      · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, le_refl]
    _ = q := by
      rw [ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

/-- info: 'XmssSecurity.TargetSum.Modes.signer_referencePhaseCounts_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCounts_bound

/-- info: 'XmssSecurity.TargetSum.Modes.signer_reference_adversaryPhase_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_reference_adversaryPhase_hashQueryBound

/-- info: 'XmssSecurity.TargetSum.Modes.signer_referencePhaseCounts_expected_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCounts_expected_bound

end XmssSecurity.TargetSum.Modes

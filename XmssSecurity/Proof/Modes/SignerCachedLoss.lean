import XmssSecurity.Proof.Modes.SignerSecondaryLoss
import XmssSecurity.Proof.Modes.SignerLimitedCoupling

/-! Assemble the seeded loss for adversaries whose forged encoding is already cached.
The remaining first-lane estimate is expressed against the source budget's explicit reserve. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Direct

def HasCachedForgedEncoding (adversary : Adversary) : Prop :=
  ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
    ∀ result ∈ support ((simulateQ romImpl
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
      result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
        (result.1.1.message, result.1.1.signature.randomness)) ≠ none

theorem HasCachedForgedEncoding.sourcePrefix {adversary : Adversary}
    (hcached : HasCachedForgedEncoding adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × CappedChain.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixExecution adversary key)) :
    result.2.1.1.1 (Concrete.CacheView.encodingInput key.secretKey.parameter result.1.epoch
      (result.1.message, result.1.signature.randomness)) ≠ none := by
  have hmaterialized : Concrete.materializeCachedKeyResult key.keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅) := by
    apply (mem_support_iff_of_evalDist_eq
      CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen _).mp
    rw [support_map]
    exact ⟨key, hkey, rfl⟩
  exact hcached (Concrete.materializeCachedKeyResult key.keyResult) hmaterialized
    ((result.1, result.2.2.toSigningLog), result.2.1.1.1)
    (Deciding.sourcePrefixExecution_phase_support adversary key result hresult)

end XmssSecurity.Direct

namespace XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_cached_seeded_loss_le (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary))) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * expectedCoupledHazards (q + 1)
        (publicLimitedAcceptedPrefixProbeExecution q (memoAdversary (Security.embed adversary))) +
      sourceSecondaryLoss (memoAdversary (Security.embed adversary)) := by
  have hfirst := (decidingFirstLane_probability_le_acceptedPrefix_of_cached _ hcached.sourcePrefix).trans
    (signer_acceptedPrefixFirstLane_probability_le_limited_expected adversary q hsmall hbound)
  apply (forgeAdvantage_deterministic_le_reference_expectedDirectSeed (Security.embed adversary)).trans
  apply (add_le_add (forgeAdvantage_le_deciding_lanes _) le_rfl).trans
  rw [add_assoc]
  exact add_le_add hfirst (prehit_add_secondLane_add_seed_le_sourceSecondaryLoss _ hcached)

theorem signer_cached_127_of_expectedHazards (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary)))
    (hhazards : expectedCoupledHazards (q + 1)
      (publicLimitedAcceptedPrefixProbeExecution q (memoAdversary (Security.embed adversary))) ≤
        (q : ℝ≥0∞) +
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) / 2 +
            expectedDirectSeedQueries (memoAdversary (Security.embed adversary)) / 2 +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  apply (signer_cached_seeded_loss_le adversary q hsmall hbound hcached).trans
  have h := add_le_add (mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) hhazards)
    (le_refl (sourceSecondaryLoss (memoAdversary (Security.embed adversary))))
  apply h.trans
  calc
    _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) / 2 +
            expectedDirectSeedQueries (memoAdversary (Security.embed adversary)) / 2 +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      add_le_add le_rfl (signer_sourceSecondaryLoss_add_reserve_le adversary q hsmall hbound)
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← mul_add]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add]
      norm_num [ENNReal.toReal_inv, digestBits]

/-- info: 'XmssSecurity.Modes.signer_cached_seeded_loss_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_cached_seeded_loss_le

/-- info: 'XmssSecurity.Modes.signer_cached_127_of_expectedHazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_cached_127_of_expectedHazards

end XmssSecurity.Modes

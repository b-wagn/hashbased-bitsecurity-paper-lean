import XmssSecurity.Proof.TargetSum.EUFCMA.FreshMixedBounds
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsEncodingCollision
import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedSecondLane
import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedDirectSeed
import XmssSecurity.Proof.TargetSum.Direct.CollisionLoss
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Assemble the two first-lane estimates with encoding prehits, the second
lane, and the expected seed loss. All query classes refer to the same execution. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Direct Deciding

noncomputable def expectedLoss (q : ℕ) (E S Z R : ℝ≥0∞) : ℝ≥0∞ :=
  ((q : ℝ≥0∞) + S + R + 41 * TargetSum.acceptanceProbability * (E + 1)) /
      ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    prehitRate * E + Z / ((2 ^ 256 : ℕ) : ℝ≥0∞)

noncomputable def terminalLoss (q : ℕ) (E S Z R : ℝ≥0∞) : ℝ≥0∞ :=
  (((q - 1 : ℕ) : ℝ≥0∞) + S + R + 2 * E + 2 * TargetSum.acceptanceProbability +
      40 * TargetSum.acceptanceProbability * (E + 1)) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    prehitRate * E + Z / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem reference_add_seed_le_expectedLoss (adversary : Generic.Adversary) (q : ℕ)
    (hsmall : q + 1 ≤ 2 ^ 127) (hbound : IsQueryBound adversary q) :
    forgeAdvantage Generic.Concrete.scheme adversary + expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      expectedLoss q (Generic.Direct.expectedDirectEncodingQueries adversary) (Generic.Direct.expectedDirectStructuralQueries adversary)
        (expectedDirectSeedQueries adversary) (expectedSigningRequests adversary) := by
  have hfirst := (freshFirstLane_probability_le_mixed_add_encoding adversary).trans
    (add_le_add (freshMixedPrefixProbability_le_expected adversary q hbound.direct)
      (freshSourceEncodingProbability_le_requests adversary))
  have htotal := (forgeAdvantage_le_fresh_deciding_lanes adversary).trans
    (add_le_add hfirst (add_le_add (winningEncodingPrehit_probability_le_prehitRate adversary q hsmall
      (isEncodingQueryBound_of_direct hbound.direct))
      (decidingSecondLane_probability_le_expected adversary)))
  apply (add_le_add htotal le_rfl).trans_eq
  simp only [expectedLoss, div_eq_mul_inv]
  ring

theorem reference_add_seed_le_terminalLoss (adversary : Generic.Adversary) (q : ℕ)
    (hpositive : 0 < q) (hsmall : q + 1 ≤ 2 ^ 127) (hbound : IsQueryBound adversary q) :
    forgeAdvantage Generic.Concrete.scheme adversary + expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      terminalLoss q (Generic.Direct.expectedDirectEncodingQueries adversary) (Generic.Direct.expectedDirectStructuralQueries adversary)
        (expectedDirectSeedQueries adversary) (expectedSigningRequests adversary) := by
  have hfirst := (freshFirstLane_probability_le_mixed_add_encoding adversary).trans
    (add_le_add (freshMixedPrefixProbability_le_terminal adversary q hpositive hbound)
      (freshSourceEncodingProbability_le_requests adversary))
  have htotal := (forgeAdvantage_le_fresh_deciding_lanes adversary).trans
    (add_le_add hfirst (add_le_add (winningEncodingPrehit_probability_le_prehitRate adversary q hsmall
      (isEncodingQueryBound_of_direct hbound.direct))
      (decidingSecondLane_probability_le_expected adversary)))
  apply (add_le_add htotal le_rfl).trans_eq
  simp only [terminalLoss, div_eq_mul_inv]
  ring

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.reference_add_seed_le_expectedLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_add_seed_le_expectedLoss

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.reference_add_seed_le_terminalLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_add_seed_le_terminalLoss

end XmssSecurity.TargetSum.EUFCMA.Requests

import XmssSecurity.Proof.EUFCMA.FreshMixedBounds
import XmssSecurity.Proof.EUFCMA.RequestsEncodingCollision
import XmssSecurity.Proof.EUFCMA.ExpectedSecondLane
import XmssSecurity.Proof.EUFCMA.ExpectedDirectSeed

/-! Assemble the two first-lane estimates with encoding prehits, the second
lane, and the expected seed loss. All query classes refer to the same execution. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA.Requests

open Direct Deciding

noncomputable def expectedLoss (q : ℕ) (E S Z R : ℝ≥0∞) : ℝ≥0∞ :=
  ((q : ℝ≥0∞) + S + R + 41 * TargetSum.acceptanceProbability * (E + 1)) /
      ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    encodingPrehitRate * E + Z / ((2 ^ 256 : ℕ) : ℝ≥0∞)

noncomputable def terminalLoss (q : ℕ) (E S Z R : ℝ≥0∞) : ℝ≥0∞ :=
  (((q - 1 : ℕ) : ℝ≥0∞) + S + R + 2 * E + 2 * TargetSum.acceptanceProbability +
      40 * TargetSum.acceptanceProbability * (E + 1)) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    encodingPrehitRate * E + Z / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem reference_add_seed_le_expectedLoss (adversary : XmssSecurity.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    forgeAdvantage Concrete.scheme adversary + expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      expectedLoss q (expectedDirectEncodingQueries adversary) (expectedDirectStructuralQueries adversary)
        (expectedDirectSeedQueries adversary) (expectedSigningRequests adversary) := by
  have hfirst := (freshFirstLane_probability_le_mixed_add_encoding adversary).trans
    (add_le_add (freshMixedPrefixProbability_le_expected adversary q hbound.direct)
      (freshSourceEncodingProbability_le_requests adversary))
  have htotal := (forgeAdvantage_le_fresh_deciding_lanes adversary).trans
    (add_le_add hfirst (add_le_add (winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
      (decidingSecondLane_probability_le_expected adversary)))
  apply (add_le_add htotal le_rfl).trans_eq
  simp only [expectedLoss, div_eq_mul_inv]
  ring

theorem reference_add_seed_le_terminalLoss (adversary : XmssSecurity.Adversary) (q : ℕ)
    (hpositive : 0 < q) (hbound : IsQueryBound adversary q) :
    forgeAdvantage Concrete.scheme adversary + expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      terminalLoss q (expectedDirectEncodingQueries adversary) (expectedDirectStructuralQueries adversary)
        (expectedDirectSeedQueries adversary) (expectedSigningRequests adversary) := by
  have hfirst := (freshFirstLane_probability_le_mixed_add_encoding adversary).trans
    (add_le_add (freshMixedPrefixProbability_le_terminal adversary q hpositive hbound)
      (freshSourceEncodingProbability_le_requests adversary))
  have htotal := (forgeAdvantage_le_fresh_deciding_lanes adversary).trans
    (add_le_add hfirst (add_le_add (winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
      (decidingSecondLane_probability_le_expected adversary)))
  apply (add_le_add htotal le_rfl).trans_eq
  simp only [terminalLoss, div_eq_mul_inv]
  ring

/-- info: 'XmssSecurity.EUFCMA.Requests.reference_add_seed_le_expectedLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_add_seed_le_expectedLoss

/-- info: 'XmssSecurity.EUFCMA.Requests.reference_add_seed_le_terminalLoss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_add_seed_le_terminalLoss

end XmssSecurity.EUFCMA.Requests

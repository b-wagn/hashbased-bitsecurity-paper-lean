import XmssSecurity.Proof.Direct.SourceLossBudget
import XmssSecurity.Proof.Direct.DecidingSecondLaneFresh

/-! All source-side secondary losses use the same budget for arbitrary adversaries;
the only additional second-lane cost is the fresh final encoding allowance. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Direct

theorem prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh (adversary : Adversary) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Deciding.DecidingChainValueRevealed execution.2 execution.1 |
        detailedGameWithCache Concrete.scheme adversary] +
      expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
        sourceSecondaryLoss adversary + Deciding.forgedEncodingFreshProbability adversary *
          (Checksum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  apply (add_le_add (add_le_add (winningEncodingPrehit_probability_le_expected_direct_encoding adversary)
    (Deciding.decidingSecondLane_probability_le_source_credit_add_fresh adversary)) le_rfl).trans_eq
  unfold sourceSecondaryLoss
  ring

/-- info: 'XmssSecurity.Direct.prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh

end XmssSecurity.Direct

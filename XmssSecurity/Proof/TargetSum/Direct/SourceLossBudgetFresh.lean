import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! All source-side secondary losses use the same budget for arbitrary adversaries;
the only additional second-lane cost is the fresh final encoding allowance. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Direct

theorem prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh (adversary : Generic.Adversary)
    (hprehit : Pr[Generic.WinningEncodingPrehitOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] ≤
      prehitRate * Generic.Direct.expectedDirectEncodingQueries adversary) :
    Pr[Generic.WinningEncodingPrehitOccurs | Generic.cappedDetailedGameWithEncodingTrace adversary] +
      Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 |
        Generic.detailedGameWithCache Generic.Concrete.scheme adversary] +
      expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
        sourceSecondaryLoss adversary + Deciding.forgedEncodingFreshProbability adversary *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  apply (add_le_add (add_le_add hprehit
    (Deciding.decidingSecondLane_probability_le_source_credit_add_fresh adversary)) le_rfl).trans_eq
  unfold sourceSecondaryLoss
  ring

/-- info: 'XmssSecurity.TargetSum.Direct.prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh

end XmssSecurity.TargetSum.Direct

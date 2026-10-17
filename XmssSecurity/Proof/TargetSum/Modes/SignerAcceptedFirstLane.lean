import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedLoss

/-! The source encoding credit pays for the accepted first lane, including adversaries
that sometimes return fresh encodings. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_acceptedPrefixFirstLane_probability_le_source_credit
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 |
      sourcePrefixProgram (memoAdversary (Security.embed adversary))] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  acceptedPrefixFirstLane_probability_le_source_credit _ q
    (signer_countedSourceBudget_after_trajectory adversary q hsmall hbound)

/-- For arbitrary adversaries the fresh contribution is retained explicitly. Its
acceptance factor is established here; `Direct/TerminalMixedFirstLane.lean` bounds the
collision contribution in the complete signer-mode proof. -/
theorem signer_firstLane_probability_le_accepted_add_fresh
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    Pr[WinningDecidingFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace (memoAdversary (Security.embed adversary))] ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        TargetSum.acceptanceProbability * Pr[SourcePrefixForgedEncodingFresh |
          sourcePrefixProgram (memoAdversary (Security.embed adversary))] :=
  (decidingFirstLane_probability_le_accepted_add_fresh _).trans
    (add_le_add (signer_acceptedPrefixFirstLane_probability_le_source_credit adversary q hsmall hbound) le_rfl)

/-- info: 'XmssSecurity.TargetSum.Modes.signer_acceptedPrefixFirstLane_probability_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_acceptedPrefixFirstLane_probability_le_source_credit

/-- info: 'XmssSecurity.TargetSum.Modes.signer_firstLane_probability_le_accepted_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_firstLane_probability_le_accepted_add_fresh

end XmssSecurity.TargetSum.Modes

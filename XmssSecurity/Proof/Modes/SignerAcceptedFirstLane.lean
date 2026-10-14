import XmssSecurity.Proof.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.Direct.FreshVerificationProbability
import XmssSecurity.Proof.Modes.SignerCachedLoss

/-! The source encoding credit pays for the accepted first lane, including adversaries
that sometimes return fresh encodings. Only the subsequent cached-game assembly
requires the always-cached hypothesis. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Modes

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

theorem signer_cached_seeded_loss_le_source_credit (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary))) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) := by
  have hfirst := (decidingFirstLane_probability_le_acceptedPrefix_of_cached _ hcached.sourcePrefix).trans
    (signer_acceptedPrefixFirstLane_probability_le_source_credit adversary q hsmall hbound)
  apply (forgeAdvantage_deterministic_le_reference_expectedDirectSeed (Security.embed adversary)).trans
  apply (add_le_add (forgeAdvantage_le_deciding_lanes _) le_rfl).trans
  rw [add_assoc]
  exact add_le_add hfirst (prehit_add_secondLane_add_seed_le_sourceSecondaryLoss _ hcached)

/-- For arbitrary adversaries the fresh contribution is retained explicitly. Its
acceptance factor is established here; its collision factor remains to be bounded. -/
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

/-- info: 'XmssSecurity.Modes.signer_acceptedPrefixFirstLane_probability_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_acceptedPrefixFirstLane_probability_le_source_credit

/-- info: 'XmssSecurity.Modes.signer_cached_seeded_loss_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_cached_seeded_loss_le_source_credit

/-- info: 'XmssSecurity.Modes.signer_firstLane_probability_le_accepted_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_firstLane_probability_le_accepted_add_fresh

end XmssSecurity.Modes

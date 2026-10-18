import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedReferenceSeed
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Honest reference key generation, signing, and verification never query the
seed domain. The expected standard seed-hop loss is therefore paid by direct seed
queries in the same reference game as all other expected query classes. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Direct

private theorem expectedSeedQueries_eq_zero {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hzero : computation.IsQueryBoundP (Seeded.hashBad MaySeedHit) 0) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit) computation cache = 0 := by
  have h := expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ computation cache 0 hzero
  simpa using h

theorem expectedSeedQueries_gameRest_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (EUFCMA.gameRest Concrete.scheme adversary publicKey secretKey) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsDirectSeedQuery (adversary.main publicKey) cache := by
  unfold EUFCMA.gameRest
  rw [expectedSimulatedQueryCount_bind]
  have htail (result : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec) :
      expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (do
          let verified ← Concrete.scheme.verify publicKey result.1.epoch result.1.message result.1.signature
          pure (decide (SUFCMA.SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.ContainsRequest result.2 result.1) && verified)) cache = 0 := by
    apply expectedSeedQueries_eq_zero
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (XmssSecurity.TargetSum.Seeded.referenceVerify_noSeed _ _ _ _) (fun _ _ => OracleComp.isQueryBoundP_pure _ _ _)
  simp only [htail, mul_zero, tsum_zero, add_zero]
  exact Direct.expectedSeedQueries_adversaryPhase_eq adversary publicKey secretKey cache

theorem expectedSeedQueries_gameCore_eq (adversary : Adversary) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (gameCore Concrete.scheme adversary) ∅ = expectedDirectSeedQueries adversary := by
  unfold gameCore expectedDirectSeedQueries
  rw [expectedSimulatedQueryCount_bind,
    expectedSeedQueries_eq_zero _ _ XmssSecurity.TargetSum.Seeded.referenceKeygen_noSeed, zero_add]
  apply tsum_congr
  intro keyResult
  rw [expectedSeedQueries_gameRest_eq]

theorem forgeAdvantage_deterministic_le_reference_expectedDirectSeed (adversary : Adversary) :
    forgeAdvantage Seeded.scheme adversary ≤ forgeAdvantage Concrete.scheme (Seeded.memoAdversary adversary) +
      expectedDirectSeedQueries (Seeded.memoAdversary adversary) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  simpa only [expectedSeedQueries_gameCore_eq] using
    Seeded.forgeAdvantage_deterministic_le_reference_expectedReferenceSeed adversary

/-- info: 'XmssSecurity.TargetSum.EUFCMA.forgeAdvantage_deterministic_le_reference_expectedDirectSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedDirectSeed

end XmssSecurity.TargetSum.EUFCMA

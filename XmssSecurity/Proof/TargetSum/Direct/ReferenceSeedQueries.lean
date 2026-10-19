import XmssSecurity.Proof.TargetSum.Seeded.ReferenceNoSeed
import XmssSecurity.Proof.TargetSum.Direct.SeedQueryPartition
import XmssSecurity.Proof.TargetSum.Deterministic.ExpectedReferenceQueries
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The reference game's seed-domain queries are exactly its direct adversary queries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct

variable [Code]

private theorem expectedSeedQueries_eq_zero {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hzero : computation.IsQueryBoundP (Seeded.hashBad MaySeedHit) 0) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit) computation cache = 0 := by
  have h := expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ computation cache 0 hzero
  simpa using h

theorem expectedSeedQueries_adversaryPhase_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (Deciding.adversaryPhase adversary publicKey secretKey) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsDirectSeedQuery (adversary.main publicKey) cache := by
  have hproject := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment
    (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproject
  have hcount := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit) computation cache)
    hproject
  rw [expectedSimulatedQueryCount_map] at hcount
  unfold Deciding.adversaryPhase
  rw [hcount]
  have h := Direct.expectedSimulatedQueryCount_mappedAdversary_eq publicKey secretKey
    (Seeded.hashBad MaySeedHit)
    (fun request cache => expectedSeedQueries_eq_zero _ cache (Seeded.referenceSign_noSeed _ _ _))
    (adversary.main publicKey) cache
  convert h using 1
  congr 1
  funext input
  rcases input with (uniform | input) | request <;> rfl

theorem expectedSeedQueries_gameRest_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (Seeded.gameRest Concrete.scheme adversary publicKey secretKey) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsDirectSeedQuery (adversary.main publicKey) cache := by
  unfold Seeded.gameRest
  rw [expectedSimulatedQueryCount_bind]
  have htail (result : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec) :
      expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (do
          let verified ← Concrete.scheme.verify publicKey result.1.epoch result.1.message result.1.signature
          pure (decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified)) cache = 0 := by
    apply expectedSeedQueries_eq_zero
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (Seeded.referenceVerify_noSeed _ _ _ _) (fun _ _ => OracleComp.isQueryBoundP_pure _ _ _)
  simp only [htail, mul_zero, tsum_zero, add_zero]
  exact expectedSeedQueries_adversaryPhase_eq adversary publicKey secretKey cache

noncomputable def expectedDirectSeedQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      IsDirectSeedQuery (adversary.main keyResult.1.1) keyResult.2

theorem expectedSeedQueries_gameCore_eq (adversary : Adversary) :
    expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (gameCore Concrete.scheme adversary) ∅ = expectedDirectSeedQueries adversary := by
  unfold gameCore expectedDirectSeedQueries
  rw [expectedSimulatedQueryCount_bind,
    expectedSeedQueries_eq_zero _ _ Seeded.referenceKeygen_noSeed, zero_add]
  apply tsum_congr
  intro keyResult
  rw [expectedSeedQueries_gameRest_eq]

theorem forgeAdvantage_deterministic_le_reference_expectedDirectSeed (adversary : Adversary) :
    forgeAdvantage Seeded.scheme adversary ≤ forgeAdvantage Concrete.scheme (Seeded.memoAdversary adversary) +
      expectedDirectSeedQueries (Seeded.memoAdversary adversary) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  simpa only [expectedSeedQueries_gameCore_eq] using
    Seeded.forgeAdvantage_deterministic_le_reference_expectedReferenceSeed adversary

/-- info: 'XmssSecurity.TargetSum.Direct.forgeAdvantage_deterministic_le_reference_expectedDirectSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedDirectSeed

end XmssSecurity.TargetSum.Direct

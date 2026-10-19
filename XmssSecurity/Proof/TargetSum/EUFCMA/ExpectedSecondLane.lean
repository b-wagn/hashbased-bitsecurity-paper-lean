import XmssSecurity.Proof.TargetSum.EUFCMA.QueriedStructural
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Keep expected query counts in the second-lane bound for an arbitrary
adversary. Moving the verifier encoding into the prefix adds exactly one encoding
query and preserves the complete final execution. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Deciding Direct

theorem expectedEncodingQueries_withForgedEncodingQuery_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec)
    (hparameter : publicKey.parameter = secretKey.parameter) :
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter)
        ((Direct.withForgedEncodingQuery adversary).main publicKey) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) cache + 1 := by
  unfold Direct.withForgedEncodingQuery
  rw [expectedSimulatedQueryCount_bind]
  simp only [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_pure,
    mul_zero, tsum_zero, add_zero, Direct.IsDirectEncodingQuery, hparameter,
    encodingInputLeafIndex?_encodingInput, Option.isSome_some, if_true,
    mul_one, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)]

theorem expectedDirectEncodingQueries_withForgedEncodingQuery (adversary : Adversary) :
    Direct.expectedDirectEncodingQueries (Direct.withForgedEncodingQuery adversary) =
      Direct.expectedDirectEncodingQueries adversary + 1 := by
  unfold Direct.expectedDirectEncodingQueries
  calc
    _ = ∑' key, Pr[= key | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        (expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl key.1.1 key.1.2)
          (Direct.IsDirectEncodingQuery key.1.2.parameter) (adversary.main key.1.1) key.2 + 1) := by
      apply tsum_congr
      intro key
      by_cases hkey : key ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · rw [expectedEncodingQueries_withForgedEncodingQuery_eq adversary key.1.1 key.1.2 key.2
          (Deciding.keygen_publicKey_parameter_eq key hkey)]
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by simp only [mul_add, mul_one, ENNReal.tsum_add, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)]

theorem decidingSecondLane_probability_le_expected (adversary : Adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
        ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
        ¬ Deciding.DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Direct.expectedDirectEncodingQueries adversary + 1) *
          (TargetSum.acceptanceProbability * ((48 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by
  have hsecond := decidingSecondLane_probability_le_expectedEncoding (Direct.withForgedEncodingQuery adversary) (by
    intro key hkey result hresult
    have hcached := Direct.adversaryPhase_withForgedEncodingQuery_cached adversary key.1.1 key.1.2 key.2 result hresult
    rw [Deciding.keygen_publicKey_parameter_eq key hkey] at hcached
    exact hcached)
  rw [Direct.detailedGameWithCache_withForgedEncodingQuery,
    expectedDirectStructuralQueries_withForgedEncodingQuery,
    expectedDirectEncodingQueries_withForgedEncodingQuery] at hsecond
  exact hsecond

/-- info: 'XmssSecurity.TargetSum.EUFCMA.decidingSecondLane_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingSecondLane_probability_le_expected

end XmssSecurity.TargetSum.EUFCMA

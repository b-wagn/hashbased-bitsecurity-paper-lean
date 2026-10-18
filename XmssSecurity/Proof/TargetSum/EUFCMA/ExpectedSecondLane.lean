import XmssSecurity.Proof.TargetSum.EUFCMA.QueriedStructural
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Keep expected query counts in the second-lane bound for an arbitrary
adversary. Moving the verifier encoding into the prefix adds exactly one encoding
query and preserves the complete final execution. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Deciding Direct

theorem expectedEncodingQueries_withForgedEncodingQuery_eq (adversary : Generic.Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec)
    (hparameter : publicKey.parameter = secretKey.parameter) :
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectEncodingQuery secretKey.parameter)
        ((Generic.Direct.withForgedEncodingQuery adversary).main publicKey) cache =
      expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Generic.Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) cache + 1 := by
  unfold Generic.Direct.withForgedEncodingQuery
  rw [expectedSimulatedQueryCount_bind]
  simp only [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_pure,
    mul_zero, tsum_zero, add_zero, Generic.Direct.IsDirectEncodingQuery, hparameter,
    Generic.encodingInputLeafIndex?_encodingInput, Option.isSome_some, if_true,
    mul_one, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)]

theorem expectedDirectEncodingQueries_withForgedEncodingQuery (adversary : Generic.Adversary) :
    Generic.Direct.expectedDirectEncodingQueries (Generic.Direct.withForgedEncodingQuery adversary) =
      Generic.Direct.expectedDirectEncodingQueries adversary + 1 := by
  unfold Generic.Direct.expectedDirectEncodingQueries
  calc
    _ = ∑' key, Pr[= key | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
        (expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl key.1.1 key.1.2)
          (Generic.Direct.IsDirectEncodingQuery key.1.2.parameter) (adversary.main key.1.1) key.2 + 1) := by
      apply tsum_congr
      intro key
      by_cases hkey : key ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)
      · rw [expectedEncodingQueries_withForgedEncodingQuery_eq adversary key.1.1 key.1.2 key.2
          (Generic.Deciding.keygen_publicKey_parameter_eq key hkey)]
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by simp only [mul_add, mul_one, ENNReal.tsum_add, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)]

theorem decidingSecondLane_probability_le_expected (adversary : Generic.Adversary) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
        ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
        ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      Generic.Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Generic.Direct.expectedDirectEncodingQueries adversary + 1) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by
  have hsecond := decidingSecondLane_probability_le_expectedEncoding (Generic.Direct.withForgedEncodingQuery adversary) (by
    intro key hkey result hresult
    have hcached := Generic.Direct.adversaryPhase_withForgedEncodingQuery_cached adversary key.1.1 key.1.2 key.2 result hresult
    rw [Generic.Deciding.keygen_publicKey_parameter_eq key hkey] at hcached
    exact hcached)
  rw [Generic.Direct.detailedGameWithCache_withForgedEncodingQuery,
    expectedDirectStructuralQueries_withForgedEncodingQuery,
    expectedDirectEncodingQueries_withForgedEncodingQuery] at hsecond
  exact hsecond

/-- info: 'XmssSecurity.TargetSum.EUFCMA.decidingSecondLane_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingSecondLane_probability_le_expected

end XmssSecurity.TargetSum.EUFCMA

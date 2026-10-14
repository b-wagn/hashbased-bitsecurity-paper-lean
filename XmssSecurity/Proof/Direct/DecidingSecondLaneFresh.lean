import XmssSecurity.Proof.Direct.QueriedEncodingAcceptance
import XmssSecurity.Proof.Direct.SourceSignerQueries

/-! The second-lane acceptance bound for arbitrary adversaries. A final fresh encoding
contributes its acceptance probability, without increasing the structural query count. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open Concrete Direct

theorem decidingSecondLane_afterKeygen_le_expectedEncoding_add_fresh (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) +
      (expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
          (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 +
        Pr[fun result => result.2 (forgeryEncodingInput keyResult.1.1 result.1.1) = none |
          (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2]) *
        (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  have hparameter := keygen_publicKey_parameter_eq keyResult hkey
  have hsecond := decidingSecondLane_afterKeygen_le_expected_accepted
    (withForgedEncodingQuery adversary) keyResult hkey (fun result hresult => by
      have hcached := adversaryPhase_withForgedEncodingQuery_cached adversary keyResult.1.1 keyResult.1.2
        keyResult.2 result hresult
      rw [hparameter] at hcached
      exact hcached)
  rw [← detailedGameAfterKeygen_eq_phases,
    simulateQ_romImpl_detailedGameAfterKeygen_withForgedEncodingQuery,
    detailedGameAfterKeygen_eq_phases,
    expectedStructuralQueries_withForgedEncodingQuery_eq _ _ _ hparameter] at hsecond
  apply hsecond.trans
  apply add_le_add le_rfl
  apply (mul_le_mul' (acceptedPrefix_withForgedEncodingQuery_probability_le_expected adversary
    keyResult.1.1 keyResult.1.2 keyResult.2 (precomputedKeygen_no_acceptedEncoding keyResult hkey)) le_rfl).trans_eq
  ac_rfl

noncomputable def forgedEncodingFreshProbability (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    Pr[fun result => result.2 (forgeryEncodingInput keyResult.1.1 result.1.1) = none |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2]

theorem forgedEncodingFreshProbability_le_one (adversary : Adversary) :
    forgedEncodingFreshProbability adversary ≤ 1 := by
  unfold forgedEncodingFreshProbability
  exact tsum_probOutput_mul_le _ _ _ (fun _ => probEvent_le_one)

theorem decidingSecondLane_probability_le_expectedEncoding_add_fresh (adversary : Adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (expectedPrefixEncodingQueries adversary + forgedEncodingFreshProbability adversary) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  unfold detailedGameWithCache detailedGameCore
  simp only [detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let structural := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (IsDirectStructuralQuery keyResult.1.2 keyResult.2) (adversary.main keyResult.1.1) keyResult.2
  let encoding := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2
  let fresh := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    Pr[fun result => result.2 (forgeryEncodingInput keyResult.1.1 result.1.1) = none |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2]
  let rate := TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        (structural keyResult / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
          (encoding keyResult + fresh keyResult) * rate) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        have h := decidingSecondLane_afterKeygen_le_expectedEncoding_add_fresh adversary keyResult hkey
        rw [expectedStructuralQueries_adversaryPhase_eq] at h
        exact h
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by
      simp only [mul_add, add_mul, div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_add,
        ENNReal.tsum_mul_right]
      change expectedDirectStructuralQueries adversary * _ +
        (expectedPrefixEncodingQueries adversary * _ + forgedEncodingFreshProbability adversary * _) = _
      simp only [rate, div_eq_mul_inv]
      ring

theorem decidingSecondLane_probability_le_source_credit_add_fresh (adversary : Adversary) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary +
          forgedEncodingFreshProbability adversary) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) :=
  (decidingSecondLane_probability_le_expectedEncoding_add_fresh adversary).trans
    (add_le_add le_rfl (mul_le_mul' (add_le_add (expectedPrefixEncodingQueries_le adversary) le_rfl) le_rfl))

/-- info: 'XmssSecurity.Deciding.decidingSecondLane_probability_le_source_credit_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingSecondLane_probability_le_source_credit_add_fresh

end XmssSecurity.Deciding

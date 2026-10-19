import XmssSecurity.Proof.Checksum.NoSign.HashFreeSigned
import XmssSecurity.Proof.Checksum.NoSign.UnsignedTop
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries

/-! The exact three-query bound, retaining the probability of each signing branch. -/

open OracleComp OracleSpec ENNReal
open XmssSecurity.Generic

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

theorem hashFree_signedProbability_le_signRate (adversary : Adversary)
    (hweighted : ∀ pk, IsWeightedBound 3 (adversary.main pk) 3) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.signingLog ≠ [] |
      detailedGameWithCache Concrete.scheme (hashFree adversary)] ≤
      ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        signRate adversary keyResult.1.1 := by
  classical
  rw [probEvent_game_phases]
  refine ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl ?_
  have hlog : (∑' before, Pr[= before |
      realRun keyResult.1.2 ((hashFree adversary).main keyResult.1.1) keyResult.2] *
        Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.signingLog ≠ [] |
          (simulateQ romImpl (Deciding.verificationPhase keyResult.1.1 keyResult.1.2
            before.1)).run before.2]) =
      Pr[fun before => before.1.2 ≠ [] |
        realRun keyResult.1.2 ((hashFree adversary).main keyResult.1.1) keyResult.2] := by
    rw [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro before
    rw [Deciding.probEvent_verificationPhase_log _ _ _ _ (fun log => log ≠ [])]
    split_ifs <;> simp
  rw [hlog]
  refine (probEvent_signingLog_ne_nil_le keyResult.1.1 keyResult.1.2 _ keyResult.2).trans
    (le_of_eq ?_)
  change expectedSimulatedQueryCount _ IsSignQuery (Direct.pruneDirect 0
    (adversary.main keyResult.1.1)) keyResult.2 = _
  rw [expectedSign_pruneDirect_zero_eq _ 3 3 _ (hweighted _) le_rfl (by norm_num)]
  exact expectedSign_eq_of_uniformFaithful _ idealImpl
    (mappedImpl_uniformFaithful _ _) idealImpl_uniformFaithful 3 3 _ (hweighted _)
      le_rfl (by norm_num) _ ∅

theorem threeBudget_with_seed_le (adversary : Adversary)
    (hweighted : ∀ pk, IsWeightedBound 3 (adversary.main pk) 3) :
    forgeAdvantage Concrete.scheme adversary +
      TargetSum.Direct.expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      48 * digestInverse := by
  classical
  let keygenRun := (simulateQ romImpl Concrete.scheme.keygen).run ∅
  let count : (PublicKey × Generic.SecretKey) × QueryCache HashSpec → ℝ≥0∞ := fun keyResult =>
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2
  let rate := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    signRate adversary keyResult.1.1
  let unsigned := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    unsignedRate adversary keyResult.1.1 + idealSize adversary keyResult.1.1 +
      (count keyResult + unsignedPrefixProbability adversary keyResult)
  have hsigned : Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      execution.1.won = true ∧ execution.1.signingLog ≠ [] |
      detailedGameWithCache Concrete.scheme adversary] ≤
      48 * digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * rate keyResult := by
    rw [signed_won_eq_hashFree adversary hweighted]
    exact (hashFree_signed_probability_le (hashFree adversary)
      (fun pk => Direct.pruneDirect_isQueryBoundP 0 _)).trans
        (mul_le_mul' le_rfl (hashFree_signedProbability_le_signRate adversary hweighted))
  have hunsigned : Pr[fun execution : GameOutcome × QueryCache HashSpec =>
      execution.1.won = true ∧ execution.1.signingLog = [] |
      detailedGameWithCache Concrete.scheme adversary] ≤
      digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * unsigned keyResult := by
    unfold detailedGameWithCache detailedGameCore
    simp only [Deciding.detailedGameAfterKeygen_eq_phases]
    rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
    calc
      _ ≤ ∑' keyResult, Pr[= keyResult | keygenRun] *
          (Pr[fun before : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 before.1.1 ∧ before.1.2 = [] |
            (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
              keyResult.2] +
            digestInverse * (count keyResult + unsignedPrefixProbability adversary keyResult)) := by
        apply ENNReal.tsum_le_tsum
        intro keyResult
        by_cases hkeygen : keyResult ∈ support keygenRun
        · exact mul_le_mul' le_rfl (unsigned_top_keyResult_le adversary keyResult hkeygen)
        · change Pr[= keyResult | keygenRun] * _ ≤ Pr[= keyResult | keygenRun] * _
          simp [probOutput_eq_zero_of_not_mem_support hkeygen]
      _ = (∑' keyResult, Pr[= keyResult | keygenRun] *
            Pr[fun before : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
                HiddenSiblingGuessed keyResult.2 keyResult.1.2 before.1.1 ∧ before.1.2 = [] |
              (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
                keyResult.2]) +
          digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            (count keyResult + unsignedPrefixProbability adversary keyResult) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        exact tsum_congr fun keyResult => by ring
      _ ≤ digestInverse * (∑' keyResult, Pr[= keyResult | keygenRun] *
            (unsignedRate adversary keyResult.1.1 + idealSize adversary keyResult.1.1)) +
          digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
            (count keyResult + unsignedPrefixProbability adversary keyResult) := by
        apply add_le_add _ le_rfl
        dsimp only [keygenRun]
        rw [tsum_scheme_keygen_publicKey (fun pk => unsignedRate adversary pk + idealSize adversary pk)]
        exact hiddenSibling_unsigned_guard_le adversary
      _ = _ := by
        rw [← mul_add, ← ENNReal.tsum_add]
        congr 1
        exact tsum_congr fun keyResult => by simp only [unsigned]; ring
  have hseed : TargetSum.Direct.expectedDirectSeedQueries adversary /
      ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * count keyResult := by
    rw [TargetSum.Direct.expectedDirectSeedQueries, div_eq_mul_inv, mul_comm]
    apply mul_le_mul'
    · apply ENNReal.inv_le_inv.mpr
      exact_mod_cast (show (2 : ℕ) ^ digestBits ≤ 2 ^ 256 from by
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num [digestBits]))
    · apply ENNReal.tsum_le_tsum
      intro keyResult
      exact mul_le_mul' le_rfl (expectedSimulatedQueryCount_mono _ _ _
        TargetSum.Direct.directSeed_isDirectHashQuery _ _)
  have hpointwise : ∀ keyResult, 48 * rate keyResult + unsigned keyResult + count keyResult ≤ 48 := by
    intro keyResult
    let σ := rate keyResult
    have hideal : idealSize adversary keyResult.1.1 + 3 * σ ≤ 3 := by
      refine (add_le_add (idealSize_le adversary keyResult.1.1) le_rfl).trans ?_
      unfold forwardPhase
      rw [expectedWorldHash_forwardOnly_eq]
      exact_mod_cast expected_direct_add_sign_le idealImpl 3 3 _ (hweighted _) ∅
    have hdirect : count keyResult + 3 * σ ≤ 3 := by
      have h := expected_direct_add_sign_le
        (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2) 3 3
        (adversary.main keyResult.1.1) (hweighted keyResult.1.1) keyResult.2
      rw [expectedSign_eq_of_uniformFaithful _ idealImpl
        (mappedImpl_uniformFaithful _ _) idealImpl_uniformFaithful 3 3 _ (hweighted _)
          le_rfl (by norm_num) _ ∅] at h
      exact_mod_cast h
    have hu : unsignedRate adversary keyResult.1.1 + σ ≤ 1 :=
      marked_unsigned_add_sign_le 3 3 _ (hweighted _) le_rfl (by norm_num) ∅
    have hv : unsignedPrefixProbability adversary keyResult + σ ≤ 1 :=
      unsignedPrefix_add_signRate_le adversary hweighted keyResult
    have hσ : σ ≤ 1 := (le_add_self : σ ≤ unsignedRate adversary keyResult.1.1 + σ).trans hu
    calc
      _ = 37 * σ + (idealSize adversary keyResult.1.1 + 3 * σ) +
          2 * (count keyResult + 3 * σ) + (unsignedRate adversary keyResult.1.1 + σ) +
          (unsignedPrefixProbability adversary keyResult + σ) := by
        dsimp only [unsigned, σ]
        ring
      _ ≤ 37 * 1 + 3 + 2 * 3 + 1 + 1 := by gcongr
      _ = 48 := by norm_num
  rw [forgeAdvantage_eq_detailedGameWithCache]
  have hsplit : Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.won = true |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog ≠ [] |
        detailedGameWithCache Concrete.scheme adversary] +
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog = [] |
        detailedGameWithCache Concrete.scheme adversary] := by
    refine (probEvent_mono fun execution _ hwin => ?_).trans (probEvent_or_le _ _ _)
    by_cases hlog : execution.1.signingLog = []
    · exact Or.inr ⟨hwin, hlog⟩
    · exact Or.inl ⟨hwin, hlog⟩
  calc
    _ ≤ (48 * digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * rate keyResult) +
        (digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * unsigned keyResult) +
        (digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] * count keyResult) :=
      add_le_add (hsplit.trans (add_le_add hsigned hunsigned)) hseed
    _ = digestInverse * ∑' keyResult, Pr[= keyResult | keygenRun] *
        (48 * rate keyResult + unsigned keyResult + count keyResult) := by
      simp only [mul_add, ENNReal.tsum_add]
      simp_rw [mul_left_comm _ (48 : ℝ≥0∞), ENNReal.tsum_mul_left]
      ring
    _ ≤ digestInverse * 48 := mul_le_mul' le_rfl
      (Direct.tsum_probOutput_mul_le _ _ _ hpointwise)
    _ = _ := mul_comm _ _

theorem signerRequests_three_advantage_le (adversary : Security.StatementAdversary)
    (hbound : (SUFCMA.notion ⟨false, true, false, true⟩).HasQueryBound Generic.xmss adversary 3) :
    (SUFCMA.notion ⟨false, true, false, true⟩).advantage Generic.xmss adversary ≤
      48 * digestInverse := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq,
    forgeAdvantage_pruneWeighted_eq adversary true 3 hbound]
  refine (TargetSum.Direct.forgeAdvantage_deterministic_le_reference_expectedDirectSeed _).trans
    (threeBudget_with_seed_le _ fun publicKey => ?_)
  exact memoize_isWeightedBound 3 3 _ ∅ (pruneWeighted_isWeightedBound _ _ _)

/-- info: 'XmssSecurity.Checksum.NoSign.signerRequests_three_advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signerRequests_three_advantage_le

end XmssSecurity.Checksum.NoSign

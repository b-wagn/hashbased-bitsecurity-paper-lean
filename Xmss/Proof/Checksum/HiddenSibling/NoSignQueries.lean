import Xmss.Proof.Checksum.HiddenSibling.TopCollision
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-!
# Forgeries without signing requests

An adversary that requests no signature and makes at most `D` direct hash queries forges with
probability at most `(2D + 2) / 2^128` (`forgeAdvantage_le_of_noSignQueries`): an accepted forgery
either forges the honest top sibling (`hiddenSibling_le`) or makes a fresh top query collide with
the root (`topFresh_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.Checksum.HiddenSibling

/-- The top collision, summed over key generation. -/
theorem topFresh_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hno : NoSignQueries adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
      Pr[fun execution : GameOutcome × QueryCache HashSpec =>
          RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
            (topTarget keyResult.1.2 keyResult.2) |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
          Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
  refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun keyResult hkeygen => ?_
  refine (RandomOracle.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ _
    fun _ _ hcollision => hcollision).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul' ?_ le_rfl
  have h := expected_top_le adversary D hD hno keyResult
    (Deciding.keygen_publicKey_parameter_eq keyResult hkeygen)
  exact_mod_cast h

/-- The hidden top sibling, summed over the game's key generation. -/
theorem hiddenSibling_scheme_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hno : NoSignQueries adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
  have hdist : 𝒟[(simulateQ romImpl precomputedScheme.keygen).run ∅] =
      𝒟[Keygen.materializeCachedKeyResult <$> (simulateQ romImpl Keygen.keygen).run ∅] := by
    rw [Keygen.evalDist_materialized_keygen_eq_precomputedKeygen]
    rfl
  calc
    _ = ∑' keyResult, Pr[= keyResult | Keygen.materializeCachedKeyResult <$>
            (simulateQ romImpl Keygen.keygen).run ∅] *
          Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
            (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1
              keyResult.1.2)).run keyResult.2] :=
      tsum_congr fun keyResult => by rw [probOutput_congr rfl hdist]
    _ = ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Keygen.keygen).run ∅] *
          Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
            (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1
              keyResult.1.2)).run keyResult.2] := by
      rw [tsum_probOutput_map_mul]
      refine tsum_congr fun keyResult => ?_
      refine congrArg₂ (fun (p q : ℝ≥0∞) => p * q) rfl ?_
      simp only [adversaryPhase_eq_of_noSign adversary hno, simulateQ_map, StateT.run_map,
        probEvent_map, Keygen.materializeCachedKeyResult_publicKey,
        Keygen.materializeCachedKeyResult_cache, Keygen.materializeCachedKeyResult_secretKey,
        HiddenSiblingGuessed,
        Keygen.materializePrecomputation_parameter, Keygen.materializePrecomputation_chainStart]
    _ ≤ _ := hiddenSibling_le adversary D hD hno

/-- An adversary without signing requests and with `D` direct hash queries forges with
probability at most `(2D + 2) / 2^128`. -/
theorem forgeAdvantage_le_of_noSignQueries (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hno : NoSignQueries adversary) :
    forgeAdvantage precomputedScheme adversary ≤ ((2 * D + 2 : ℕ) : ℝ≥0∞) * digestInverse := by
  rw [forgeAdvantage_eq_detailedGameWithCache]
  unfold detailedGameWithCache detailedGameCore
  simp only [Deciding.detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let rest := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
      Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
          (Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
            (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1
              keyResult.1.2)).run keyResult.2] +
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
                (topTarget keyResult.1.2 keyResult.2) | rest keyResult]) := by
      refine ENNReal.tsum_le_tsum fun keyResult => ?_
      by_cases hkeygen : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)
      swap
      · rw [probOutput_eq_zero_of_not_mem_support hkeygen, zero_mul, zero_mul]
      refine mul_le_mul' le_rfl ?_
      have hrest : rest keyResult =
          (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1
            keyResult.1.2)).run keyResult.2 >>= fun prefixResult =>
            (simulateQ romImpl (Deciding.verificationPhase keyResult.1.1 keyResult.1.2
              prefixResult.1)).run prefixResult.2 := by
        simp only [rest, simulateQ_bind, StateT.run_bind]
      calc
        _ ≤ Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 execution.1.forgery ∨
                RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
                  (topTarget keyResult.1.2 keyResult.2) | rest keyResult] := by
          refine probEvent_mono fun execution hexecution hwin => ?_
          change execution ∈ support (rest keyResult) at hexecution
          rw [hrest, mem_support_bind_iff] at hexecution
          obtain ⟨prefixResult, hprefix, hafter⟩ := hexecution
          have hforgery := (Deciding.verificationPhase_support _ _ _ _ _ hafter).2.2.1
          rw [hforgery]
          exact topCases adversary keyResult hkeygen prefixResult hprefix execution hafter hwin
        _ ≤ Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 execution.1.forgery |
              rest keyResult] +
            Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
                (topTarget keyResult.1.2 keyResult.2) | rest keyResult] :=
          probEvent_or_le _ _ _
        _ ≤ _ := by
          refine add_le_add ?_ le_rfl
          rw [hrest]
          refine probEvent_bind_le_of_imp _ _ _ _ fun prefixResult _ execution hafter hguess => ?_
          have hforgery := (Deciding.verificationPhase_support _ _ _ _ _ hafter).2.2.1
          rwa [hforgery] at hguess
    _ = (∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
          Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
            (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1
              keyResult.1.2)).run keyResult.2]) +
        ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
          Pr[fun execution : GameOutcome × QueryCache HashSpec =>
              RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
                (topTarget keyResult.1.2 keyResult.2) | rest keyResult] := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun keyResult => mul_add _ _ _
    _ ≤ ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse + ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse :=
      add_le_add (hiddenSibling_scheme_le adversary D hD hno) (topFresh_le adversary D hD hno)
    _ = ((2 * D + 2 : ℕ) : ℝ≥0∞) * digestInverse := by
      rw [← add_mul, ← Nat.cast_add]
      congr 2
      omega

/-- info: 'Xmss.Checksum.HiddenSibling.forgeAdvantage_le_of_noSignQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_le_of_noSignQueries

end Xmss.Checksum.HiddenSibling

import Xmss.Proof.Checksum.HiddenSibling.ThreeBudget
import Xmss.Proof.Checksum.HiddenSibling.UnsignedForward

/-! On an unsigned execution, only one verifier query can collide at the top address. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

noncomputable def unsignedPrefixProbability (adversary : Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) : ℝ≥0∞ :=
  Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
      prefixResult.1.2 = [] |
    (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
      keyResult.2]

theorem unsignedPrefix_add_signRate_le (adversary : Adversary)
    (hweighted : ∀ pk, IsWeightedBound 3 (adversary.main pk) 3)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) :
    unsignedPrefixProbability adversary keyResult + signRate adversary keyResult.1.1 ≤ 1 := by
  have hunsigned := probEvent_realRun_noSign_le_marked keyResult.1.2
    (adversary.main keyResult.1.1) keyResult.2 (fun _ => True)
  simp only [true_and] at hunsigned
  have hcount := marked_unsigned_add_sign_le 3 3 (adversary.main keyResult.1.1)
    (hweighted _) le_rfl (by norm_num) keyResult.2
  rw [expectedSign_eq_of_uniformFaithful idealImpl idealImpl idealImpl_uniformFaithful
    idealImpl_uniformFaithful 3 3 _ (hweighted _) le_rfl (by norm_num) keyResult.2 ∅] at hcount
  exact (add_le_add hunsigned le_rfl).trans hcount

theorem unsigned_top_keyResult_le (adversary : Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ execution.1.signingLog = [] |
      (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
            prefixResult.1.2 = [] |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] +
      digestInverse * (expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 +
          unsignedPrefixProbability adversary keyResult) := by
  classical
  let prefixRun := (simulateQ romImpl
    (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  let event : GameOutcome × QueryCache HashSpec → Prop := fun execution =>
    execution.1.won = true ∧ execution.1.signingLog = []
  let guessed : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun before => HiddenSiblingGuessed keyResult.2 keyResult.1.2 before.1.1 ∧ before.1.2 = []
  let collision : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun before => RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 before.2
      (topTarget keyResult.1.2 keyResult.2)
  have hpointwise : ∀ before ∈ support prefixRun,
      Pr[event | (simulateQ romImpl
          (Deciding.verificationPhase keyResult.1.1 keyResult.1.2 before.1)).run before.2] ≤
        (if guessed before then 1 else 0) + (if collision before then 1 else 0) +
          digestInverse * (if before.1.2 = [] then 1 else 0) := by
    intro before hbefore
    by_cases hlog : before.1.2 = []
    swap
    · rw [probEvent_eq_zero fun after hafter hevent => hlog (by
        rw [← (Deciding.verificationPhase_support _ _ _ _ _ hafter).2.2.2.1]
        exact hevent.2)]
      exact zero_le
    by_cases hguess : guessed before
    · rw [if_pos hguess]
      exact probEvent_le_one.trans (le_add_of_le_left (le_add_right le_rfl))
    by_cases hcollision : collision before
    · rw [if_neg hguess, zero_add, if_pos hcollision]
      exact probEvent_le_one.trans le_self_add
    rw [if_neg hguess, if_neg hcollision, zero_add, zero_add, if_pos hlog, mul_one]
    calc
      _ ≤ expectedSimulatedQueryCount romImpl
          (RandomOracle.IsRelevantHashQuery fun input => topTarget keyResult.1.2 keyResult.2 input ≠ input)
          (Deciding.verificationPhase keyResult.1.1 keyResult.1.2 before.1) before.2 /
            ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
        apply RandomOracle.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
        intro after hafter hwin
        have hfresh := (topCases adversary keyResult hkeygen before hbefore after hafter
          hwin.1).resolve_left (fun h => hguess ⟨h, hlog⟩)
        exact Deciding.adaptiveFreshCollision_split _ _ _ _
          (xmssRom_cache_le _ _ _ hbefore) (xmssRom_cache_le _ _ _ hafter) hfresh hcollision
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        change _ * digestInverse ≤ digestInverse
        suffices expectedSimulatedQueryCount romImpl
            (RandomOracle.IsRelevantHashQuery fun input => topTarget keyResult.1.2 keyResult.2 input ≠ input)
            (Deciding.verificationPhase keyResult.1.1 keyResult.1.2 before.1) before.2 ≤ 1 by
          simpa using mul_le_mul' this (le_refl digestInverse)
        refine (expectedSimulatedQueryCount_mono romImpl _
          (RandomOracle.IsRelevantHashQuery (AtHashAddress keyResult.1.2.parameter
            (.merkle topLevel Generic.Merkle.rootNode))) (fun input hinput => ?_) _ _).trans ?_
        · rcases input with _ | input
          · exact hinput.elim
          · exact atTop_of_topTarget_ne _ _ input hinput
        · rw [Deciding.expectedQueries_verificationPhase_eq]
          have hbound := scheme_verify_top_one keyResult.1.1 before.1.1.epoch
            before.1.1.message before.1.1.signature
          rw [Deciding.keygen_publicKey_parameter_eq keyResult hkeygen] at hbound
          exact_mod_cast expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ _ 1 hbound
  have hprefixCollision : Pr[collision | prefixRun] ≤ digestInverse *
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 := by
    refine (RandomOracle.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ collision
      (fun _ _ h => h)).trans ?_
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul' le_rfl ?_
    refine (expectedSimulatedQueryCount_mono romImpl _
      (RandomOracle.IsRelevantHashQuery (AtHashAddress keyResult.1.2.parameter
        (.merkle topLevel Generic.Merkle.rootNode))) (fun input hinput => ?_) _ _).trans ?_
    · rcases input with _ | input
      · exact hinput.elim
      · exact atTop_of_topTarget_ne _ _ input hinput
    · rw [expectedQueries_adversaryPhase_eq _ keyResult.1.2
        (fun leaf payload => not_top_encodingInput _ leaf payload)]
      exact expectedDirectWorld_le_direct _ _ _ _
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' before, Pr[= before | prefixRun] *
        ((if guessed before then 1 else 0) + (if collision before then 1 else 0) +
          digestInverse * (if before.1.2 = [] then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hbefore : before ∈ support prefixRun
      · exact mul_le_mul' le_rfl (hpointwise before hbefore)
      · change Pr[= before | prefixRun] * _ ≤ Pr[= before | prefixRun] * _
        simp only [probOutput_eq_zero_of_not_mem_support hbefore, zero_mul, le_refl]
    _ = Pr[guessed | prefixRun] + Pr[collision | prefixRun] +
        digestInverse * unsignedPrefixProbability adversary keyResult := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · congr 1 <;> rw [probEvent_eq_tsum_ite] <;>
          apply tsum_congr <;> intro before <;> split_ifs <;> simp
      · rw [unsignedPrefixProbability, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro before
        split_ifs <;> simp [mul_comm, prefixRun]
    _ ≤ _ := by
      calc
        _ ≤ Pr[guessed | prefixRun] + digestInverse *
            expectedSimulatedQueryCount
              (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
              Direct.IsDirectHashQuery (adversary.main keyResult.1.1) keyResult.2 +
            digestInverse * unsignedPrefixProbability adversary keyResult :=
          add_le_add (add_le_add le_rfl hprefixCollision) le_rfl
        _ = _ := by rw [mul_add, add_assoc]

end Xmss.Checksum.HiddenSibling

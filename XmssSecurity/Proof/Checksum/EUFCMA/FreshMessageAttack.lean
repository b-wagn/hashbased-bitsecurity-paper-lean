import XmssSecurity.Proof.Checksum.Attack.FreshMessage
import XmssSecurity.Proof.Common.EUFCMA.Modes

/-!
# Standard forgeries on a fresh message

The adversary that requests one signature and submits it for a fresh message
(`Attack/FreshMessage.lean`) wins with probability above `2^-123`. Its request is fresh, so it
wins the standard game whenever it wins the strong one. It is charged `1` when the requests are
charged, `2` when the signer is, and `3` when both are, which refutes `123`, `124`, and `125` bits
of standard unforgeability in these modes.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open SUFCMA

attribute [local irreducible] sampleMasterSeed

noncomputable abbrev freshSufCmaAdversary :
    SUFCMA.Adversary OracleWorld PublicKey Message Signature lifetime :=
  oneRequestSufCmaAdversary freshMessageForgery

theorem freshMessage_queryBound (signer requests : Bool) :
    (EUFCMA.notion ⟨false, signer, false, requests⟩).HasQueryBound xmss freshSufCmaAdversary
      ((if requests then 1 else 0) + (if signer then 2 else 0)) := by
  apply (EUFCMA.hasQueryBound_iff_strong _ _ _ _).2
  intro result hresult
  exact oneRequest_counted_support_bound _ signer requests result
    (support_simulateQ_run'_subset romImpl _ ∅ hresult)

theorem freshMessage_strong_advantage (mode : CountingMode) :
    (SUFCMA.notion mode).advantage xmss freshSufCmaAdversary =
      forgeAdvantage Seeded.scheme freshAdversary := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  rfl

/-- Every strong win of the fresh-message adversary is a standard win. -/
theorem freshMessage_strong_le_standard :
    (SUFCMA.notion ⟨false, false, false, true⟩).advantage xmss freshSufCmaAdversary ≤
      (EUFCMA.notion ⟨false, false, false, true⟩).advantage xmss freshSufCmaAdversary := by
  unfold SecurityNotion.advantage
  rw [EUFCMA.experiment_eq_map_recordedExperiment,
    EUFCMA.strong_experiment_eq_map_recordedExperiment, probEvent_map, probEvent_map]
  apply probEvent_mono
  intro outcome houtcome hwin
  have hgame := support_simulateQ_run'_subset romImpl _ ∅ houtcome
  unfold EUFCMA.recordedGame at hgame
  simp only [costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero] at hgame
  have hmain := fun (secretKey : Seeded.SecretKey) =>
    oneRequestMain_counted_zero xmss secretKey 1 freshMessageForgery mutationChoice
  simp only [show freshSufCmaAdversary.main =
    fun _ => oneRequestMain freshMessageForgery mutationChoice from rfl, hmain] at hgame
  simp only [bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
    bind_assoc, pure_bind] at hgame
  obtain ⟨keyResult, _, answer, _, choice, _, verified, _, rfl⟩ := hgame
  simp only [Function.comp_apply, EUFCMA.CountedOutcome.strongResult,
    EUFCMA.CountedOutcome.standardResult, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  exact ⟨⟨hwin.1.1, freshMessage_request_fresh answer choice⟩, hwin.2⟩

theorem freshMessage_standard_advantage_lower (mode : CountingMode) :
    forgeAdvantage Seeded.scheme freshAdversary ≤
      (EUFCMA.notion mode).advantage xmss freshSufCmaAdversary := by
  rw [EUFCMA.advantage_eq_of_mode _ ⟨false, false, false, true⟩,
    ← freshMessage_strong_advantage ⟨false, false, false, true⟩]
  exact freshMessage_strong_le_standard

theorem freshMessage_attack (signer requests : Bool) (bits : ℕ)
    (hratio : (((if requests then 1 else 0) + (if signer then 2 else 0) : ℕ) : ℝ≥0∞) /
      ((2 ^ bits : ℕ) : ℝ≥0∞) ≤ 1 / ((2 ^ 123 : ℕ) : ℝ≥0∞))
    (hpositive : 1 ≤ (if requests then 1 else 0) + (if signer then 2 else 0)) :
    ¬(EUFCMA.notion ⟨false, signer, false, requests⟩).HasClassicalSecurityBits xmss bits := by
  intro hsecure
  have hbound := hsecure _ hpositive freshSufCmaAdversary (freshMessage_queryBound signer requests)
  exact (not_lt_of_ge ((freshMessage_standard_advantage_lower _).trans (hbound.trans hratio)))
    fresh_seeded_advantage_exceeds_123

theorem freshMessage_requests_attack :
    ¬(EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1) :=
  freshMessage_attack false true 123 (by norm_num) (by norm_num)

theorem freshMessage_signer_attack :
    ¬(EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss (123 + 1) := by
  apply freshMessage_attack true false 124 _ (by norm_num)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem freshMessage_signerRequests_attack :
    ¬(EUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss (124 + 1) := by
  apply freshMessage_attack true true 125 _ (by norm_num)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- info: 'XmssSecurity.Checksum.Attack.freshMessage_signerRequests_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshMessage_signerRequests_attack

end XmssSecurity.Checksum.Attack

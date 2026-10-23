import Xmss.Proof.TargetSum.EUFCMA.RequestsTerminalProbe
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Couple terminal activity with the cached fresh first-lane event. Divergent
activity is charged to the same collision and cancels from the final bound. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Requests
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding FirstLaneOracleSimulation

theorem activity_coupling_afterKeygen (adversary : Adversary) (q : ℕ)
    (hbound : Direct.IsDirectQueryBound adversary q)
    (left : CappedExecution.ProgrammedGlobalChainKeygenView) (right : Deciding.BaseKey)
    (hkey : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleft : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (Deciding.sourcePrefixExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2) (Deciding.publicPrefixExecution adversary right.1)).run)
      (fun source target =>
        (FreshPrefixFirstLaneEvent left source → encodingActive left.secretKey.parameter source.2.2 = true ∧
          FirstLaneOracleSimulation.CombinedHit right.2 (appendFreshPrefixProbe q right.2 right.1 target).2) ∧
        (PublicExtra right.1 target.1 → encodingActive left.secretKey.parameter source.2.2 = true ∨
          FirstLaneOracleSimulation.CombinedHit right.2 (appendFreshPrefixProbe q right.2 right.1 target).2)) := by
  have hpk : left.publicKey = right.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := CappedExecution.relTriple_sourceExact_firstLane_adversary_boundedHit_direct q q le_rfl adversary
    left right hkey hleft hright (hbound left.publicKey)
  have hrightProgram : (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      (Deciding.publicPrefixExecution adversary right.1)).run =
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((simulateQ (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl right.1)
        (adversary.main left.publicKey)).run
          (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState right.1)))).run := by
    unfold Deciding.publicPrefixExecution
    rw [hpk]
  rw [hrightProgram]
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  have hactivity := sourcePrefix_freshAccepted_encoded adversary left hleft source hresult.2.1
  rcases hresult.1 with ⟨hforgery, hgood, hcount⟩ | hhit
  · have hacceptance := sourcePublic_freshAccepted_iff left right hkey hleft hright source target hforgery hgood
    have hparameter := CappedExecution.programmedGlobal_secretKey_parameter_eq left right hkey hleft hright
    have htrace : source.2.2 = target.1.2.attackerTrace := hgood.1.2
    constructor
    · intro hevent
      refine ⟨hactivity hevent.2, ?_⟩
      rw [appendFreshPrefixProbe, if_pos (hacceptance.mp hevent.2),
        FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le _ q hcount]
      have hsupport := hresult.2.2
      rw [hpk] at hsupport
      have hcovered := CappedExecution.globalFirstLaneAdversary_support_returnedCovered right.1 right.2
        (adversary.main right.1.publicKey) target hsupport
      exact Deciding.prefixFirstLaneEvent_good_implies_hit left right hkey hleft hright source target
        hforgery hgood hcovered hevent.1
    · rintro (hactive | hfresh)
      · exact Or.inl (by simpa only [hparameter, htrace] using hactive)
      · exact Or.inl (hactivity (hacceptance.mpr hfresh))
  · have hprobed : FirstLaneOracleSimulation.CombinedHit right.2 (appendFreshPrefixProbe q right.2 right.1 target).2 := by
      unfold appendFreshPrefixProbe
      split
      · exact FirstLaneOracleSimulation.CombinedHit.append_of_prefix _ _ _ hhit
      · exact hhit
    exact ⟨fun hevent => ⟨hactivity hevent.2, hprobed⟩, fun _ => Or.inr hprobed⟩

theorem activity_coupling (adversary : Adversary) (q : ℕ)
    (hbound : Direct.IsDirectQueryBound adversary q) :
    RelTriple (Deciding.sourcePrefixProgram adversary) (Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary))
      (fun source target =>
        (FreshPrefixFirstLaneEvent source.1 source.2 → SourcePrefixEncoded source ∧ CoupledFreshProbedHit q target) ∧
        (CoupledExtra target → SourcePrefixEncoded source ∨ CoupledFreshProbedHit q target)) := by
  unfold Deciding.sourcePrefixProgram Deciding.coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    CappedExecution.relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_stable)
  intro left right hkeys
  obtain ⟨hkey, hleft, hright⟩ := hkeys
  apply relTriple_bind (activity_coupling_afterKeygen adversary q hbound left right hkey hleft
    (CappedExecution.coupledGlobalChainKeygenWithBaseFull_support_keyView right hright))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem freshPrefixFirstLane_probability_le_terminal (adversary : Adversary) (q : ℕ)
    (hpositive : 0 < q) (hbound : IsQueryBound adversary q) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Deciding.sourcePrefixProgram adversary] ≤
      ((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (2 * Direct.expectedDirectEncodingQueries adversary) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  rw [← sourcePrefixProgram_stopped_freshFirstLane_eq adversary q hbound]
  have h := accepted_event_probability_le_of_relTriple
    (source := Deciding.sourcePrefixProgram (stoppedAdversary q adversary))
    (target := Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution (stoppedAdversary q adversary)))
    (fun result => FreshPrefixFirstLaneEvent result.1 result.2) SourcePrefixEncoded CoupledExtra (CoupledFreshProbedHit q)
    (2 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹)
    (((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, digestBits])
    (activity_coupling (stoppedAdversary q adversary) q hbound.stopped.direct)
    (stopped_probedHit_probability_le adversary q hpositive hbound)
  rw [sourcePrefixProgram_stopped_encodingActivity_eq adversary q hbound] at h
  apply h.trans
  apply add_le_add le_rfl
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul' (le_refl (2 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
      (sourcePrefixProgram_encodingActivity_probability_le adversary)

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.freshPrefixFirstLane_probability_le_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshPrefixFirstLane_probability_le_terminal

end Xmss.TargetSum.EUFCMA.Requests

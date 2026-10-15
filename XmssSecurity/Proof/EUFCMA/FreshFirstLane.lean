import XmssSecurity.Proof.EUFCMA.FreshProbe
import XmssSecurity.Proof.AcceptedEventCoupling

/-! Couple the fresh first-lane event and its acceptance gate together. The
collision contribution on divergent executions cancels the extra probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

theorem sourcePublic_freshAccepted_iff
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (source : Forgery × SourceExactTracedState)
    (target : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hforgery : source.1 = target.1.1)
    (hgood : SourceFirstLaneExactGoodStateRelation left right.1 source.2 target.1.2 target.2) :
    SourcePrefixFreshAccepted left source ↔ PublicFreshAccepted right.1.1 target.1 := by
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hkey hleft hright
  have htrace : source.2.2 = target.1.2.attackerTrace := hgood.1.2
  obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
  change GlobalFilteredCausalStateRelation left right.1 source.2.1.1.1 target.1.2.causalState at hcausal
  have hencoding : forgedEncoding source.2.1.1.1 left.secretKey.parameter source.1 =
      forgedEncoding target.1.2.causalState.cache right.1.1.secretKey.parameter target.1.1 := by
    rw [hparameter, ← hforgery]
    exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
  constructor
  · rintro ⟨hfresh, encoding, hdecode⟩
    refine ⟨by simpa only [← htrace, ← hforgery] using hfresh, ?_⟩
    rw [← hencoding]
    exact Option.isSome_iff_exists.mpr ⟨encoding, hdecode⟩
  · rintro ⟨hfresh, haccepted⟩
    rw [← hencoding] at haccepted
    exact ⟨by simpa only [htrace, hforgery] using hfresh, Option.isSome_iff_exists.mp haccepted⟩

theorem freshPrefix_acceptance_coupling_afterKeygen
    (adversary : XmssSecurity.Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2) (publicPrefixExecution adversary right.1.1 right.2)).run)
      (fun source target =>
        (FreshPrefixFirstLaneEvent left source → SourcePrefixFreshAccepted left source ∧
          CombinedHit right.1.2 (appendFreshPrefixProbe D right.1.2 right.1.1 target).2) ∧
        (PublicFreshAccepted right.1.1 target.1 → SourcePrefixFreshAccepted left source ∨
          CombinedHit right.1.2 (appendFreshPrefixProbe D right.1.2 right.1.1 target).2)) := by
  have hpk : left.publicKey = right.1.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := relTriple_sourceExact_firstLane_adversary_boundedHit_direct D D le_rfl adversary
    left right hkey hleft hright (hD left.publicKey)
  have hrightProgram : (simulateQ (eagerTraceImpl right.1.2)
      (publicPrefixExecution adversary right.1.1 right.2)).run =
    (simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        (adversary.main left.publicKey)).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run := by
    unfold publicPrefixExecution
    rw [hpk]
  rw [hrightProgram]
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  rcases hresult.1 with ⟨hforgery, hgood, hcount⟩ | hhit
  · have hacceptance := sourcePublic_freshAccepted_iff left right hkey hleft hright source target hforgery hgood
    constructor
    · intro hevent
      refine ⟨hevent.2, ?_⟩
      rw [appendFreshPrefixProbe, if_pos (hacceptance.mp hevent.2),
        enforceHazardTrace_eq_self_of_count_le _ D hcount]
      have hsupport := hresult.2.2
      rw [hpk] at hsupport
      have hcovered := globalFirstLaneAdversary_support_returnedCovered right.1.1 right.1.2
        right.2 (adversary.main right.1.1.publicKey) target hsupport
      exact prefixFirstLaneEvent_good_implies_hit left right hkey hleft hright source target
        hforgery hgood hcovered hevent.1
    · exact fun haccepted => Or.inl (hacceptance.mpr haccepted)
  · have hprobed : CombinedHit right.1.2 (appendFreshPrefixProbe D right.1.2 right.1.1 target).2 := by
      unfold appendFreshPrefixProbe
      split
      · exact CombinedHit.append_of_prefix _ _ _ hhit
      · exact hhit
    exact ⟨fun hevent => ⟨hevent.2, hprobed⟩, fun _ => Or.inr hprobed⟩

theorem freshPrefix_acceptance_coupling (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    RelTriple (sourcePrefixProgram adversary) (coupledFirstLaneProgram (publicPrefixExecution adversary))
      (fun source target =>
        (FreshPrefixFirstLaneEvent source.1 source.2 → SourcePrefixFreshAccepted source.1 source.2 ∧
          CoupledFreshProbedHit D target) ∧
        (CoupledPrefixFreshAccepted target → SourcePrefixFreshAccepted source.1 source.2 ∨
          CoupledFreshProbedHit D target)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleft, hright⟩ := hkeys
  apply relTriple_bind (freshPrefix_acceptance_coupling_afterKeygen adversary D hD left right hkey hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem sourcePrefixProgram_freshAccepted_probability_le (adversary : XmssSecurity.Adversary)
    (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => SourcePrefixFreshAccepted result.1 result.2 | sourcePrefixProgram adversary] ≤
      TargetSum.acceptanceProbability * (D : ℝ≥0∞) := by
  unfold sourcePrefixProgram
  apply probEvent_bind_le_of_forall_le
  intro key hkey
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  exact sourcePrefix_freshAccepted_probability_le adversary key hkey D hD

theorem freshPrefixFirstLane_probability_le (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability * D) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply (accepted_event_probability_le_of_relTriple
    (source := sourcePrefixProgram adversary)
    (target := coupledFirstLaneProgram (publicPrefixExecution adversary))
    (fun result => FreshPrefixFirstLaneEvent result.1 result.2)
    (fun result => SourcePrefixFreshAccepted result.1 result.2)
    CoupledPrefixFreshAccepted (CoupledFreshProbedHit D)
    (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ((D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (by norm_num [digestBits])
    (freshPrefix_acceptance_coupling adversary D hD) (coupledFreshProbedHit_probability_le adversary D)).trans
  apply add_le_add le_rfl
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul'
    (le_refl (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
    (sourcePrefixProgram_freshAccepted_probability_le adversary D hD)

/-- info: 'XmssSecurity.EUFCMA.freshPrefixFirstLane_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshPrefixFirstLane_probability_le

end XmssSecurity.EUFCMA

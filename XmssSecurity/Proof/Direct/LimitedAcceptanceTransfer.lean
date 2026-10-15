import XmssSecurity.Proof.Direct.SourcePrefixAcceptance

/-! Accepted ideal prefixes come from an accepted source cache or a recorded collision.
This transfers an event probability without identifying post-collision costs. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity

theorem probEvent_le_source_add_bad_of_relTriple {α β : Type}
    {source : ProbComp α} {target : ProbComp β}
    (sourceEvent : α → Prop) (targetEvent bad : β → Prop)
    (hrel : RelTriple source target (fun left right => targetEvent right → sourceEvent left ∨ bad right)) :
    Pr[targetEvent | target] ≤ Pr[sourceEvent | source] + Pr[bad | target] := by
  classical
  calc
    _ ≤ Pr[fun result => (targetEvent result ∧ ¬bad result) ∨ bad result | target] := by
      apply probEvent_mono''
      intro result hresult
      by_cases hbad : bad result
      · exact Or.inr hbad
      · exact Or.inl ⟨hresult, hbad⟩
    _ ≤ Pr[fun result => targetEvent result ∧ ¬bad result | target] + Pr[bad | target] := probEvent_or_le _ _ _
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply probEvent_le_of_relTriple (relTriple_symm hrel)
      intro right left hpost hevent
      exact (hpost hevent.1).resolve_right hevent.2

namespace Deciding

open CappedChain FirstLaneOracleSimulation

theorem limitedPrefix_acceptance_coupling_afterKeygen (adversary : Adversary) (limit : Nat)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (adversary.main left.publicKey) (CountedSourceState.initial left.cache)) :
    RelTriple (sourceCountedPrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicLimitedPrefixExecution limit adversary right.1.1 right.2)).run)
      (fun source target => LimitedPrefixForgedEncodingAccepted right.1.1 target →
        HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∨ CombinedHit right.1.2 target.2) := by
  have hcoupling := relTriple_countedSource_limitedPrefix left right hrel hleft hright limit
    (adversary.main left.publicKey) hbudget
  have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
  change RelTriple (sourceCountedPrefixExecution adversary left)
    ((simulateQ (eagerTraceImpl right.1.2) (limitedFirstLanePrefix limit right.1.1 right.2
      (adversary.main left.publicKey)
      (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run) _ at hcoupling
  rw [hpk] at hcoupling
  apply relTriple_post_mono hcoupling
  intro source target hresult haccepted
  rcases hresult.2.2.2.2 with ⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit
  · simp only [List.nil_append] at hgood
    obtain ⟨completed, hcompleted, haccepted⟩ := haccepted
    rw [hvalue] at hcompleted
    cases hcompleted
    have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 =
        forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1 := by
      rw [hparameter]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    rw [← hencoding] at haccepted
    obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp haccepted
    exact Or.inl (hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode)
  · exact Or.inr (by simpa only [List.nil_append] using hhit)

theorem limitedPrefix_acceptance_coupling (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    RelTriple (sourceCountedPrefixProgram adversary)
      (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))
      (fun source target => CoupledLimitedPrefixAccepted target →
        SourceCountedPrefixAccepted source ∨ CoupledLimitedPrefixHit target) := by
  unfold sourceCountedPrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hrel, hleft, hright⟩ := hkeys
  apply relTriple_bind (limitedPrefix_acceptance_coupling_afterKeygen adversary limit left right hrel hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) (hbudget left hleft))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem coupledLimitedPrefix_accepted_probability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[CoupledLimitedPrefixAccepted | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] ≤
      TargetSum.acceptanceProbability *
        (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary) +
        (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (probEvent_le_source_add_bad_of_relTriple SourceCountedPrefixAccepted CoupledLimitedPrefixAccepted
    CoupledLimitedPrefixHit (limitedPrefix_acceptance_coupling adversary limit hbudget)).trans
      (add_le_add (sourceCountedPrefix_accepted_probability_le adversary)
        (coupledLimitedPrefix_hit_probability_le limit adversary))

theorem expectedCoupledLimitedProbe_hazards_le_source_credit (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    expectedCoupledHazards (limit + 1) (publicLimitedAcceptedPrefixProbeExecution limit adversary) ≤
      (limit : ℝ≥0∞) + (TargetSum.acceptanceProbability *
        (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary) +
        (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)) :=
  (expectedCoupledLimitedProbe_hazards_le limit adversary).trans
    (add_le_add le_rfl (coupledLimitedPrefix_accepted_probability_le adversary limit hbudget))

/-- info: 'XmssSecurity.Deciding.expectedCoupledLimitedProbe_hazards_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedCoupledLimitedProbe_hazards_le_source_credit

end Deciding
end XmssSecurity

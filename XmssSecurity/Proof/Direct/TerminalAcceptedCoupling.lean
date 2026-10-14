import XmssSecurity.Proof.Direct.TerminalPrunedCoupling

/-! The terminal cut preserves the accepted-prefix cancellation coupling: every
cached first-lane witness still produces a hit, and a cut performs no deciding probe. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicTerminalPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  terminalPrunedFirstLanePrefix limit key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

theorem terminalPrefix_acceptance_cancellation_coupling_afterKeygen (adversary : Adversary) (limit : Nat)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (adversary.main left.publicKey) (CountedSourceState.initial left.cache)) :
    RelTriple (sourceCountedPrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicTerminalPrefixExecution limit adversary right.1.1 right.2)).run)
      (fun source target =>
        (AcceptedPrefixFirstLaneEvent left (source.1, source.2.toSource) →
          HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∧
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2) ∧
        (LimitedPrefixForgedEncodingAccepted right.1.1 target →
          HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∨
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2)) := by
  have hcoupling := relTriple_countedSource_terminalPrefix left right hrel hleft hright limit
    (adversary.main left.publicKey) hbudget
  have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
  change RelTriple (sourceCountedPrefixExecution adversary left)
    ((simulateQ (eagerTraceImpl right.1.2) (terminalPrunedFirstLanePrefix limit right.1.1 right.2
      (adversary.main left.publicKey)
      (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run) _ at hcoupling
  rw [hpk] at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  rcases hresult.1 with (⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit) | ⟨hnone, hrejecting⟩
  · simp only [List.nil_append] at hgood
    have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 =
        forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1 := by
      rw [hparameter]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    constructor
    · intro hevent
      refine ⟨acceptedPrefixFirstLane_implies_accepted left source hevent, ?_⟩
      have haccepted : (forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1).isSome := by
        rw [← hencoding]
        exact hevent.2
      have hcovered := terminalPrunedFirstLanePrefix_returnedCovered right.1.2 limit right.1.1 right.2
        (adversary.main right.1.1.publicKey) ⟨0, 0, 0⟩ target (source.1, state) hresult.2.2 hvalue
      simp only [appendLimitedAcceptedPrefixProbe, hvalue, if_pos haccepted]
      exact prefixFirstLaneEvent_good_implies_hit left right hrel hleft hright
        (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered hevent.1
    · rintro ⟨completed, hcompleted, haccepted⟩
      rw [hvalue] at hcompleted
      cases hcompleted
      rw [← hencoding] at haccepted
      obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp haccepted
      exact Or.inl (hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode)
  · have hprobed := appendLimitedAcceptedPrefixProbe_preserves_hit right.1.2 right.1.1 target
      (by simpa only [List.nil_append] using hhit)
    exact ⟨fun hevent => ⟨acceptedPrefixFirstLane_implies_accepted left source hevent, hprobed⟩,
      fun _ => Or.inr hprobed⟩
  · constructor
    · intro hevent
      exact (hrejecting (acceptedPrefixFirstLane_implies_accepted left source hevent)).elim
    · rintro ⟨completed, hcompleted, _⟩
      rw [hnone] at hcompleted
      cases hcompleted

theorem terminalPrefix_acceptance_cancellation_coupling (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    RelTriple (sourceCountedPrefixProgram adversary)
      (coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary))
      (fun source target =>
        (SourceCountedPrefixFirstLane source → SourceCountedPrefixAccepted source ∧ CoupledLimitedProbedHit target) ∧
        (CoupledLimitedPrefixAccepted target → SourceCountedPrefixAccepted source ∨ CoupledLimitedProbedHit target)) := by
  unfold sourceCountedPrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hrel, hleft, hright⟩ := hkeys
  apply relTriple_bind (terminalPrefix_acceptance_cancellation_coupling_afterKeygen adversary limit left right hrel hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) (hbudget left hleft))
  intro source target hresult
  exact relTriple_pure_pure hresult

/-- info: 'XmssSecurity.Deciding.terminalPrefix_acceptance_cancellation_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrefix_acceptance_cancellation_coupling

end XmssSecurity.Deciding

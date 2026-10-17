import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCoupling
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingActivity
import XmssSecurity.Proof.TargetSum.Direct.TerminalAcceptedCoupling

/-! The extra terminal and deciding-probe charges are paid only on source executions
with encoding activity, or on traces that have already recorded a collision. -/

open OracleComp OracleSpec
open scoped Classical
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

def TerminalPrefixExtraCharge (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) : Prop :=
  limit ≤ hazardCount result.2 ∨ LimitedPrefixForgedEncodingAccepted key result

def CoupledTerminalExtraCharge (limit : Nat) (result : CoupledLimitedPrefixResult) : Prop :=
  TerminalPrefixExtraCharge limit result.1.1.1 result.2

theorem terminalPrefix_activity_cancellation_coupling_afterKeygen (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
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
          CountedSourceEncodingActivity left.secretKey.parameter source.2 ∧
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2) ∧
        (TerminalPrefixExtraCharge limit right.1.1 target →
          CountedSourceEncodingActivity left.secretKey.parameter source.2 ∨
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2)) := by
  have hcoupling := relTriple_countedSource_terminalPrefix_activity left right hrel hleft hright limit
    (adversary.main left.publicKey) hbudget
  have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
  change RelTriple (sourceCountedPrefixExecution adversary left)
    ((simulateQ (eagerTraceImpl right.1.2) (terminalPrunedFirstLanePrefix limit right.1.1 right.2
      (adversary.main left.publicKey)
      (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run) _ at hcoupling
  rw [hpk] at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  have hsourceEncoding := countedSource_encodingBudget_after_trajectory left hleft
    (adversary.main left.publicKey) source hresult.2.1
  rcases hresult.1 with (⟨state, hvalue, hgood, hcounters, _hcount⟩ | hhit) | ⟨hnone, hrejecting, hshort⟩
  · simp only [List.nil_append] at hgood
    have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel hleft hright
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    have hencoding : forgedEncoding source.2.counts.cache left.secretKey.parameter source.1 =
        forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1 := by
      rw [hparameter]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    constructor
    · intro hevent
      refine ⟨hsourceEncoding.activity_of_accepted (acceptedPrefixFirstLane_implies_accepted left source hevent), ?_⟩
      have haccepted : (forgedEncoding state.causalState.cache right.1.1.secretKey.parameter source.1).isSome := by
        rw [← hencoding]
        exact hevent.2
      have hcovered := terminalPrunedFirstLanePrefix_returnedCovered right.1.2 limit right.1.1 right.2
        (adversary.main right.1.1.publicKey) ⟨0, 0, 0⟩ target (source.1, state) hresult.2.2 hvalue
      simp only [appendLimitedAcceptedPrefixProbe, hvalue, if_pos haccepted]
      exact prefixFirstLaneEvent_good_implies_hit left right hrel hleft hright
        (source.1, source.2.toSource) ((source.1, state), target.2) rfl hgood hcovered hevent.1
    · rintro (hfull | ⟨completed, hcompleted, haccepted⟩)
      · by_cases hactivity : CountedSourceEncodingActivity left.secretKey.parameter source.2
        · exact Or.inl hactivity
        · have hrightOriginal := terminalPrunedFirstLanePrefix_success_support right.1.2 limit right.1.1 right.2
            (adversary.main right.1.1.publicKey) _ ⟨0, 0, 0⟩ target (source.1, state) hresult.2.2 hvalue
          rw [← hpk] at hrightOriginal
          have hsamples := countedSource_firstLane_encodingSamples_le left right hrel hleft hright
            (adversary.main left.publicKey) source ((source.1, state), target.2) hresult.2.1 hrightOriginal hgood
          dsimp only at hsamples
          have htrace : source.2.attackerTrace = state.attackerTrace := hgood.1.2
          have hzero : target.1.2.encoding + target.1.2.samples = 0 := by
            rw [hcounters]
            simp only [firstLaneCounters, List.nil_append]
            rw [← htrace, hparameter] at hsamples ⊢
            unfold CountedSourceEncodingActivity at hactivity
            omega
          have hstrict := terminalPrunedFirstLanePrefix_hazardCount_lt_of_no_activity right.1.2 limit
            hpositive right.1.1 hright right.2 (adversary.main right.1.1.publicKey) target hresult.2.2 hzero
          exact (Nat.not_le_of_gt hstrict hfull).elim
      · rw [hvalue] at hcompleted
        cases hcompleted
        rw [← hencoding] at haccepted
        obtain ⟨encoding, hdecode⟩ := Option.isSome_iff_exists.mp haccepted
        exact Or.inl (hsourceEncoding.activity_of_accepted (hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode))
  · have hprobed := appendLimitedAcceptedPrefixProbe_preserves_hit right.1.2 right.1.1 target
      (by simpa only [List.nil_append] using hhit)
    exact ⟨fun hevent => ⟨hsourceEncoding.activity_of_accepted (acceptedPrefixFirstLane_implies_accepted left source hevent), hprobed⟩,
      fun _ => Or.inr hprobed⟩
  · constructor
    · intro hevent
      exact (hrejecting (acceptedPrefixFirstLane_implies_accepted left source hevent)).elim
    · rintro (hfull | ⟨completed, hcompleted, _⟩)
      · simp only [List.nil_append] at hshort
        exact (Nat.not_le_of_gt hshort hfull).elim
      · rw [hnone] at hcompleted
        cases hcompleted

theorem terminalPrefix_activity_cancellation_coupling (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    RelTriple (sourceCountedPrefixProgram adversary)
      (coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary))
      (fun source target =>
        (SourceCountedPrefixFirstLane source → SourceCountedPrefixEncodingActivity source ∧ CoupledLimitedProbedHit target) ∧
        (CoupledTerminalExtraCharge limit target → SourceCountedPrefixEncodingActivity source ∨ CoupledLimitedProbedHit target)) := by
  unfold sourceCountedPrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hrel, hleft, hright⟩ := hkeys
  apply relTriple_bind (terminalPrefix_activity_cancellation_coupling_afterKeygen adversary limit hpositive left right hrel hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) (hbudget left hleft))
  intro source target hresult
  exact relTriple_pure_pure hresult

/-- info: 'XmssSecurity.TargetSum.Deciding.terminalPrefix_activity_cancellation_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrefix_activity_cancellation_coupling

end XmssSecurity.TargetSum.Deciding

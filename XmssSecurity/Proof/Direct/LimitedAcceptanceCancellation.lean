import XmssSecurity.Proof.AcceptedEventCoupling
import XmssSecurity.Proof.Direct.LimitedAcceptanceTransfer

/-! Transfer the winning and acceptance events through the same limited-prefix
coupling. Collisions on rejected source prefixes cancel their extra probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain FirstLaneOracleSimulation

def SourceCountedPrefixFirstLane (result : ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) : Prop :=
  AcceptedPrefixFirstLaneEvent result.1 (result.2.1, result.2.2.toSource)

def CoupledLimitedProbedHit (result : CoupledLimitedPrefixResult) : Prop :=
  CombinedHit result.1.1.2 (appendLimitedAcceptedPrefixProbe result.1.1.2 result.1.1.1 result.2).2

theorem acceptedPrefixFirstLane_implies_accepted (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × CountedSourceState)
    (hevent : AcceptedPrefixFirstLaneEvent key (result.1, result.2.toSource)) :
    HasAcceptedEncoding key.secretKey.parameter result.2.counts.cache := by
  obtain ⟨encoding, hencoding⟩ := Option.isSome_iff_exists.mp hevent.2
  exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hencoding

theorem limitedPrefix_acceptance_cancellation_coupling_afterKeygen (adversary : Adversary) (limit : Nat)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleft : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hright : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (adversary.main left.publicKey) (CountedSourceState.initial left.cache)) :
    RelTriple (sourceCountedPrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicLimitedPrefixExecution limit adversary right.1.1 right.2)).run)
      (fun source target =>
        (AcceptedPrefixFirstLaneEvent left (source.1, source.2.toSource) →
          HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∧
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2) ∧
        (LimitedPrefixForgedEncodingAccepted right.1.1 target →
          HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache ∨
            CombinedHit right.1.2 (appendLimitedAcceptedPrefixProbe right.1.2 right.1.1 target).2)) := by
  have hcoupling := relTriple_countedSource_limitedPrefix left right hrel hleft hright limit
    (adversary.main left.publicKey) hbudget
  have hpk : left.publicKey = right.1.1.publicKey := hrel.1.toStable.1.2.1
  change RelTriple (sourceCountedPrefixExecution adversary left)
    ((simulateQ (eagerTraceImpl right.1.2) (limitedFirstLanePrefix limit right.1.1 right.2
      (adversary.main left.publicKey)
      (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run) _ at hcoupling
  rw [hpk] at hcoupling
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro source target hresult
  rcases hresult.1.2.2.2.2 with ⟨state, hvalue, hgood, _hcounters, _hcount⟩ | hhit
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
      have hcovered := limitedFirstLanePrefix_returnedCovered right.1.2 limit right.1.1 right.2
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

theorem limitedPrefix_acceptance_cancellation_coupling (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    RelTriple (sourceCountedPrefixProgram adversary)
      (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))
      (fun source target =>
        (SourceCountedPrefixFirstLane source → SourceCountedPrefixAccepted source ∧ CoupledLimitedProbedHit target) ∧
        (CoupledLimitedPrefixAccepted target → SourceCountedPrefixAccepted source ∨ CoupledLimitedProbedHit target)) := by
  unfold sourceCountedPrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hrel, hleft, hright⟩ := hkeys
  apply relTriple_bind (limitedPrefix_acceptance_cancellation_coupling_afterKeygen adversary limit left right hrel hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) (hbudget left hleft))
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem coupledLimitedProbedHit_probability_le (adversary : Adversary) (limit : Nat) :
    Pr[CoupledLimitedProbedHit | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
          Pr[CoupledLimitedPrefixAccepted | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] := by
  have hevent : Pr[CoupledLimitedProbedHit |
      coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] =
      Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (limit + 1) result.2.2) |
        coupledFirstLaneProgram (publicLimitedAcceptedPrefixProbeExecution limit adversary)] := by
    calc
      _ = Pr[fun result => CombinedHit result.1.1.2 result.2.2 |
          coupledFirstLaneProgram (publicLimitedAcceptedPrefixProbeExecution limit adversary)] := by
        rw [coupledLimitedAcceptedProbe_eq_map, probEvent_map]
        rfl
      _ = _ := by
        apply probEvent_congr' (fun result hresult => ?_) rfl
        unfold coupledFirstLaneProgram at hresult
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
        obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
        rw [enforceHazardTrace_eq_self_of_count_le _ _
          (limitedAcceptedPrefixProbe_trace_bound key.1.2 limit key.1.1 key.2
            (adversary.main key.1.1.publicKey) outcome houtcome)]
  rw [hevent]
  apply (coupled_enforcedHit_probability_le_expected (limit + 1) _).trans
  simpa only [mul_add, div_eq_mul_inv, mul_comm] using
    mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
      (expectedCoupledLimitedProbe_hazards_le limit adversary)

theorem sourceCountedPrefixFirstLane_probability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[SourceCountedPrefixFirstLane | sourceCountedPrefixProgram adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (Checksum.acceptanceProbability *
          (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary)) /
            ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (accepted_event_probability_le_of_relTriple SourceCountedPrefixFirstLane SourceCountedPrefixAccepted
    CoupledLimitedPrefixAccepted CoupledLimitedProbedHit _ _ (by norm_num [digestBits])
    (limitedPrefix_acceptance_cancellation_coupling adversary limit hbudget)
    (coupledLimitedProbedHit_probability_le adversary limit)).trans
  simpa only [div_eq_mul_inv, mul_comm] using add_le_add
    (le_refl ((limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))
    (mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
      (sourceCountedPrefix_accepted_probability_le adversary))

theorem sourceCountedPrefixProgram_source_projection (adversary : Adversary) :
    (fun result : ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState) =>
      (result.1, (result.2.1, result.2.2.toSource))) <$> sourceCountedPrefixProgram adversary =
        sourcePrefixProgram adversary := by
  unfold sourceCountedPrefixProgram sourcePrefixProgram
  simp only [map_bind, bind_pure_comp]
  apply bind_congr
  intro key
  rw [← comp_map]
  change (fun result : Forgery × CountedSourceState => (key, (result.1, result.2.toSource))) <$>
    sourceCountedPrefixExecution adversary key = _
  rw [show (fun result : Forgery × CountedSourceState => (key, (result.1, result.2.toSource))) =
    (fun result => (key, result)) ∘ Prod.map id CountedSourceState.toSource from rfl, comp_map]
  unfold sourceCountedPrefixExecution
  rw [countedSource_source_projection key.publicKey]
  rfl

theorem acceptedPrefixFirstLane_probability_le_source_credit (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (Checksum.acceptanceProbability *
          (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary)) /
            ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  exact sourceCountedPrefixFirstLane_probability_le adversary limit hbudget

/-- info: 'XmssSecurity.Deciding.acceptedPrefixFirstLane_probability_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedPrefixFirstLane_probability_le_source_credit

end XmssSecurity.Deciding

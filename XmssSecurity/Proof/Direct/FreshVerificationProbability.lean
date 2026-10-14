import XmssSecurity.Proof.Direct.VerificationAcceptance
import XmssSecurity.Proof.Direct.DecidingAcceptedProbe

/-! Preserve the fresh-encoding acceptance factor through the actual verification
phase and the instrumented source finisher, including events selected by a prefix. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity

theorem prefix_event_bind_probability_le {α β : Type} (head : ProbComp α)
    (tail : α → ProbComp β) (event : α → Prop) (win : α → β → Prop) (bound : ℝ≥0∞)
    (hbound : ∀ result ∈ support head, event result → Pr[win result | tail result] ≤ bound) :
    Pr[fun result : α × β => event result.1 ∧ win result.1 result.2 | do
      let result ← head
      let outcome ← tail result
      pure (result, outcome)] ≤ bound * Pr[event | head] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  by_cases hresult : result ∈ support head
  · by_cases hevent : event result
    · simp only [hevent, if_true, true_and]
      rw [mul_comm bound]
      exact mul_le_mul' le_rfl (hbound result hresult hevent)
    · simp only [hevent, false_and, if_false, mul_zero]
      rw [probEvent_eq_zero (fun _ _ h => h), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp only [zero_mul, ite_self, mul_zero, le_refl]

namespace Deciding

open Direct CappedChain

theorem verificationPhase_winning_probability_le_verified (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec) :
    Pr[fun result => result.1.won = true |
      (simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run cache] ≤
      Pr[fun result => result.1 = true | (simulateQ romImpl (Concrete.scheme.verify publicKey
        prefixResult.1.epoch prefixResult.1.message prefixResult.1.signature)).run cache] := by
  unfold verificationPhase
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, probEvent_map]
  apply probEvent_mono
  intro result _ hwin
  exact (GameOutcome.won_eq_true_iff _).mp hwin |>.2.2

theorem verificationPhase_winning_probability_le_acceptance_of_fresh (publicKey : PublicKey)
    (secretKey : SecretKey) (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hfresh : cache (forgeryEncodingInput publicKey prefixResult.1) = none) :
    Pr[fun result => result.1.won = true |
      (simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run cache] ≤
        TargetSum.acceptanceProbability :=
  (verificationPhase_winning_probability_le_verified publicKey secretKey prefixResult cache).trans
    (verify_probability_le_acceptance_of_fresh _ _ _ _ _ hfresh)

theorem verificationPhase_winning_probability_le_acceptance_of_noAcceptedEncoding (publicKey : PublicKey)
    (secretKey : SecretKey) (prefixResult : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding publicKey.parameter cache) :
    Pr[fun result => result.1.won = true |
      (simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run cache] ≤
        TargetSum.acceptanceProbability :=
  (verificationPhase_winning_probability_le_verified publicKey secretKey prefixResult cache).trans
    (verify_probability_le_acceptance_of_noAcceptedEncoding _ _ _ _ _ hcache)

theorem SourceWinningDecidingFirstLaneEvent.verified
    (key : ProgrammedGlobalChainKeygenView) (result : (Forgery × Bool) × SourceExactTracedState)
    (hevent : SourceWinningDecidingFirstLaneEvent (key, result)) : result.1.2 = true := by
  have hwin : (cappedBothEncodingProjection (sourceGlobalExactProgramResult (key, result))).1.won = true := by
    rcases hevent with hencoding | hchain
    · exact hencoding.1.1
    · exact hchain.1
  exact (GameOutcome.won_eq_true_iff _).mp hwin |>.2.2

theorem sourcePrefixFinish_firstLane_probability_le_verified (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState) :
    Pr[fun result => SourceWinningDecidingFirstLaneEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      Pr[fun result => result.1 = true | (simulateQ romImpl (Concrete.scheme.verify key.publicKey
        prefixResult.1.epoch prefixResult.1.message prefixResult.1.signature)).run prefixResult.2.1.1.1] := by
  rw [sourcePrefixFinish, probEvent_map]
  apply probEvent_mono
  intro result _ hevent
  exact hevent.verified

theorem sourcePrefixFinish_firstLane_probability_le_acceptance_of_fresh (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState)
    (hfresh : prefixResult.2.1.1.1 (forgeryEncodingInput key.publicKey prefixResult.1) = none) :
    Pr[fun result => SourceWinningDecidingFirstLaneEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      TargetSum.acceptanceProbability :=
  (sourcePrefixFinish_firstLane_probability_le_verified key prefixResult).trans
    (verify_probability_le_acceptance_of_fresh _ _ _ _ _ hfresh)

theorem sourcePrefixFinish_firstLane_probability_le_acceptance_of_noAcceptedEncoding
    (key : ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × SourceExactTracedState)
    (hcache : ¬HasAcceptedEncoding key.publicKey.parameter prefixResult.2.1.1.1) :
    Pr[fun result => SourceWinningDecidingFirstLaneEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      TargetSum.acceptanceProbability :=
  (sourcePrefixFinish_firstLane_probability_le_verified key prefixResult).trans
    (verify_probability_le_acceptance_of_noAcceptedEncoding _ _ _ _ _ hcache)

/-- The prefix can include auxiliary randomness, such as the other execution in a coupling. -/
theorem sourceFirstLane_prefix_event_probability_le {α : Type} (head : ProbComp α)
    (key : α → ProgrammedGlobalChainKeygenView) (prefixResult : α → Forgery × SourceExactTracedState)
    (event : α → Prop)
    (hrejecting : ∀ result ∈ support head, event result →
      ¬HasAcceptedEncoding (key result).publicKey.parameter (prefixResult result).2.1.1.1) :
    Pr[fun result : α × ((Forgery × Bool) × SourceExactTracedState) =>
        event result.1 ∧ SourceWinningDecidingFirstLaneEvent (key result.1, result.2) | do
      let result ← head
      let outcome ← sourcePrefixFinish (key result) (prefixResult result)
      pure (result, outcome)] ≤ TargetSum.acceptanceProbability * Pr[event | head] :=
  prefix_event_bind_probability_le _ _ _ _ _ (fun result hresult hevent =>
    sourcePrefixFinish_firstLane_probability_le_acceptance_of_noAcceptedEncoding _ _
      (hrejecting result hresult hevent))

theorem sourceFirstLane_fresh_prefix_event_probability_le {α : Type} (head : ProbComp α)
    (key : α → ProgrammedGlobalChainKeygenView) (prefixResult : α → Forgery × SourceExactTracedState)
    (event : α → Prop)
    (hfresh : ∀ result ∈ support head, event result →
      (prefixResult result).2.1.1.1 (forgeryEncodingInput (key result).publicKey (prefixResult result).1) = none) :
    Pr[fun result : α × ((Forgery × Bool) × SourceExactTracedState) =>
        event result.1 ∧ SourceWinningDecidingFirstLaneEvent (key result.1, result.2) | do
      let result ← head
      let outcome ← sourcePrefixFinish (key result) (prefixResult result)
      pure (result, outcome)] ≤ TargetSum.acceptanceProbability * Pr[event | head] :=
  prefix_event_bind_probability_le _ _ _ _ _ (fun result hresult hevent =>
    sourcePrefixFinish_firstLane_probability_le_acceptance_of_fresh _ _ (hfresh result hresult hevent))

def SourcePrefixForgedEncodingFresh
    (result : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) : Prop :=
  result.2.2.1.1.1 (forgeryEncodingInput result.1.publicKey result.2.1) = none

theorem sourcePrefixFinish_firstLane_probability_le_accepted_add_fresh (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key)) :
    Pr[fun result => SourceWinningDecidingFirstLaneEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      (if AcceptedPrefixFirstLaneEvent key prefixResult then 1 else 0) +
        (if SourcePrefixForgedEncodingFresh (key, prefixResult) then TargetSum.acceptanceProbability else 0) := by
  classical
  by_cases haccepted : AcceptedPrefixFirstLaneEvent key prefixResult
  · rw [if_pos haccepted]
    exact le_add_right probEvent_le_one
  rw [if_neg haccepted, zero_add]
  by_cases hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)
  · rw [if_pos hfresh]
    exact sourcePrefixFinish_firstLane_probability_le_acceptance_of_fresh key prefixResult hfresh
  rw [if_neg hfresh]
  apply le_of_eq
  apply probEvent_eq_zero
  intro result hresult hevent
  apply haccepted
  apply sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix _ result hresult hevent
  have hparameter := keygen_parameter_eq key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  change key.publicKey.parameter = key.secretKey.parameter at hparameter
  change prefixResult.2.1.1.1 (Concrete.CacheView.encodingInput key.publicKey.parameter
    prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none at hfresh
  rw [hparameter] at hfresh
  exact hfresh

theorem decidingFirstLane_probability_le_accepted_add_fresh (adversary : Adversary) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] +
        TargetSum.acceptanceProbability * Pr[SourcePrefixForgedEncodingFresh | sourcePrefixProgram adversary] := by
  classical
  rw [decidingFirstLane_probability_eq_source, sourceProgram_eq_prefix_finish, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  by_cases hresult : result ∈ support (sourcePrefixProgram adversary)
  · have hsupport := hresult
    unfold sourcePrefixProgram at hsupport
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
    obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hsupport
    have h := mul_le_mul' (le_refl (Pr[= (key, prefixResult) | sourcePrefixProgram adversary]))
      (sourcePrefixFinish_firstLane_probability_le_accepted_add_fresh adversary key hkey prefixResult hprefix)
    apply h.trans_eq
    rw [mul_add]
    congr 1
    · split_ifs <;> simp only [mul_one, mul_zero]
    · split_ifs <;> simp only [mul_zero, zero_mul, mul_comm]
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp only [zero_mul, ite_self, mul_zero, add_zero, le_refl]

/-- info: 'XmssSecurity.Deciding.sourceFirstLane_prefix_event_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceFirstLane_prefix_event_probability_le

/-- info: 'XmssSecurity.Deciding.sourceFirstLane_fresh_prefix_event_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceFirstLane_fresh_prefix_event_probability_le

/-- info: 'XmssSecurity.Deciding.decidingFirstLane_probability_le_accepted_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_accepted_add_fresh

end Deciding
end XmssSecurity

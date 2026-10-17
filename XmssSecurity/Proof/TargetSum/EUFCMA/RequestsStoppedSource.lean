import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsActivity

/-! The terminal stop preserves source-prefix activity and the cached fresh
first-lane event. No claim about the entire forgery game is needed here. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def stoppedFallback : Forgery := ⟨⟨0, by norm_num [lifetime, treeHeight]⟩, 0, ⟨0, fun _ => 0, fun _ => 0⟩⟩

noncomputable def stoppedAdversary (q : ℕ) (adversary : XmssSecurity.TargetSum.Adversary) : XmssSecurity.TargetSum.Adversary where
  main := fun publicKey => stopInactive (activity publicKey.parameter) q false stoppedFallback
    (adversary.main publicKey)

theorem IsQueryBound.stopped {adversary : XmssSecurity.TargetSum.Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : IsQueryBound (stoppedAdversary q adversary) q :=
  fun publicKey => stopInactive_isQueryBound _ q false stoppedFallback _ (h publicKey)

theorem sourceExact_activity_step (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceExactTracedState)
    (hresult : result ∈ support ((cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    traceActive secretKey.parameter result.2.2 =
      (traceActive secretKey.parameter state.2 || activity secretKey.parameter input) := by
  simp only [cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact traceActive_append_fragment _ _ _ _

theorem sourcePrefix_stopped_event_eq (adversary : XmssSecurity.TargetSum.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (event : Forgery × SourceExactTracedState → Prop)
    (hgate : ∀ result, event result → traceActive key.secretKey.parameter result.2.2 = true) :
    Pr[event | sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[event | sourcePrefixExecution adversary key] := by
  have hparameter : key.publicKey.parameter = key.secretKey.parameter :=
    keygen_parameter_eq key.keyResult (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have h := probEvent_stopInactive_eq
    (cappedBothTracedMappedAdversaryImpl key.publicKey (materializePrecomputation key.cache key.secretKey))
    (activity key.secretKey.parameter) (activity_charged key.secretKey.parameter)
    (fun state : SourceExactTracedState => traceActive key.secretKey.parameter state.2)
    (sourceExact_activity_step key.publicKey (materializePrecomputation key.cache key.secretKey))
    event hgate stoppedFallback (adversary.main key.publicKey) q ((((key.cache, []), []), []))
    (hbound key.publicKey)
  simpa only [sourcePrefixExecution, stoppedAdversary, hparameter,
    show traceActive key.secretKey.parameter [] = false from rfl] using h

def SourcePrefixActive (result : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) : Prop :=
  traceActive result.1.secretKey.parameter result.2.2.2 = true

theorem sourcePrefixProgram_stopped_activity_eq (adversary : XmssSecurity.TargetSum.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[SourcePrefixActive | sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[SourcePrefixActive | sourcePrefixProgram adversary] := by
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def, SourcePrefixActive]
    rw [sourcePrefix_stopped_event_eq adversary q hbound key hkey _ (fun _ h => h)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem sourcePrefix_stopped_freshFirstLane_eq (adversary : XmssSecurity.TargetSum.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen) :
    Pr[FreshPrefixFirstLaneEvent key | sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[FreshPrefixFirstLaneEvent key | sourcePrefixExecution adversary key] := by
  let event := fun result : Forgery × SourceExactTracedState =>
    FreshPrefixFirstLaneEvent key result ∧ traceActive key.secretKey.parameter result.2.2 = true
  have heq (adv : XmssSecurity.TargetSum.Adversary) :
      Pr[FreshPrefixFirstLaneEvent key | sourcePrefixExecution adv key] =
        Pr[event | sourcePrefixExecution adv key] := by
    apply probEvent_congr' (fun result hresult => ?_) rfl
    exact ⟨fun h => ⟨h, sourcePrefix_freshAccepted_active adv key hkey result hresult h.2⟩, And.left⟩
  rw [heq, heq]
  exact sourcePrefix_stopped_event_eq adversary q hbound key hkey event (fun _ h => h.2)

theorem sourcePrefixProgram_stopped_freshFirstLane_eq (adversary : XmssSecurity.TargetSum.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 |
      sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] := by
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def]
    rw [sourcePrefix_stopped_freshFirstLane_eq adversary q hbound key hkey]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefixProgram_stopped_freshFirstLane_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_stopped_freshFirstLane_eq

end XmssSecurity.TargetSum.EUFCMA.Requests

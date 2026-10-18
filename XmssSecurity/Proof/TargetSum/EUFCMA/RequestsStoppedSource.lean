import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsActivity
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The terminal stop preserves source-prefix activity and the cached fresh
first-lane event. No claim about the entire forgery game is needed here. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

def stoppedFallback : Generic.Forgery := ⟨⟨0, by norm_num [lifetime, treeHeight]⟩, 0, ⟨0, fun _ => 0, fun _ => 0⟩⟩

noncomputable def stoppedAdversary (q : ℕ) (adversary : Generic.Adversary) : Generic.Adversary where
  main := fun publicKey => stopInactive (activity publicKey.parameter) q false stoppedFallback
    (adversary.main publicKey)

theorem IsQueryBound.stopped {adversary : Generic.Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : IsQueryBound (stoppedAdversary q adversary) q :=
  fun publicKey => stopInactive_isQueryBound _ q false stoppedFallback _ (h publicKey)

theorem sourceExact_activity_step (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : Generic.CappedChain.SourceExactTracedState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.SourceExactTracedState)
    (hresult : result ∈ support ((Generic.CappedChain.cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    traceActive secretKey.parameter result.2.2 =
      (traceActive secretKey.parameter state.2 || activity secretKey.parameter input) := by
  simp only [Generic.CappedChain.cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact traceActive_append_fragment _ _ _ _

theorem sourcePrefix_stopped_event_eq (adversary : Generic.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (event : Generic.Forgery × Generic.CappedChain.SourceExactTracedState → Prop)
    (hgate : ∀ result, event result → traceActive key.secretKey.parameter result.2.2 = true) :
    Pr[event | Generic.Deciding.sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[event | Generic.Deciding.sourcePrefixExecution adversary key] := by
  have hparameter : key.publicKey.parameter = key.secretKey.parameter :=
    Generic.CappedChain.keygen_parameter_eq key.keyResult (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have h := probEvent_stopInactive_eq
    (Generic.CappedChain.cappedBothTracedMappedAdversaryImpl key.publicKey (Generic.Concrete.materializePrecomputation key.cache key.secretKey))
    (activity key.secretKey.parameter) (activity_charged key.secretKey.parameter)
    (fun state : Generic.CappedChain.SourceExactTracedState => traceActive key.secretKey.parameter state.2)
    (sourceExact_activity_step key.publicKey (Generic.Concrete.materializePrecomputation key.cache key.secretKey))
    event hgate stoppedFallback (adversary.main key.publicKey) q ((((key.cache, []), []), []))
    (hbound key.publicKey)
  simpa only [Generic.Deciding.sourcePrefixExecution, stoppedAdversary, hparameter,
    show traceActive key.secretKey.parameter [] = false from rfl] using h

theorem sourcePrefix_stopped_freshFirstLane_eq (adversary : Generic.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    Pr[FreshPrefixFirstLaneEvent key | Generic.Deciding.sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[FreshPrefixFirstLaneEvent key | Generic.Deciding.sourcePrefixExecution adversary key] := by
  let event := fun result : Generic.Forgery × Generic.CappedChain.SourceExactTracedState =>
    FreshPrefixFirstLaneEvent key result ∧ traceActive key.secretKey.parameter result.2.2 = true
  have heq (adv : Generic.Adversary) :
      Pr[FreshPrefixFirstLaneEvent key | Generic.Deciding.sourcePrefixExecution adv key] =
        Pr[event | Generic.Deciding.sourcePrefixExecution adv key] := by
    apply probEvent_congr' (fun result hresult => ?_) rfl
    exact ⟨fun h => ⟨h, sourcePrefix_freshAccepted_active adv key hkey result hresult h.2⟩, And.left⟩
  rw [heq, heq]
  exact sourcePrefix_stopped_event_eq adversary q hbound key hkey event (fun _ h => h.2)

theorem sourcePrefixProgram_stopped_freshFirstLane_eq (adversary : Generic.Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 |
      Generic.Deciding.sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Generic.Deciding.sourcePrefixProgram adversary] := by
  unfold Generic.Deciding.sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def]
    rw [sourcePrefix_stopped_freshFirstLane_eq adversary q hbound key hkey]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefixProgram_stopped_freshFirstLane_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_stopped_freshFirstLane_eq

end XmssSecurity.TargetSum.EUFCMA.Requests

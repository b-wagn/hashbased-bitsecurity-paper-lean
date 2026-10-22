import Xmss.Proof.TargetSum.EUFCMA.RequestsActivity
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The terminal stop preserves source-prefix activity and the cached fresh
first-lane event. No claim about the entire forgery game is needed here. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Requests
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

def stoppedFallback : Forgery := ⟨⟨0, by norm_num [lifetime, treeHeight]⟩, 0, ⟨0, fun _ => 0, fun _ => 0⟩⟩

noncomputable def stoppedAdversary (q : ℕ) (adversary : Adversary) : Adversary where
  main := fun publicKey => stopInactive (activity publicKey.parameter) q false stoppedFallback
    (adversary.main publicKey)

theorem IsQueryBound.stopped {adversary : Adversary} {q : ℕ}
    (h : IsQueryBound adversary q) : IsQueryBound (stoppedAdversary q adversary) q :=
  fun publicKey => stopInactive_isQueryBound _ q false stoppedFallback _ (h publicKey)

theorem sourceExact_activity_step (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CappedExecution.SourceExactTracedState)
    (result : (OracleWorld + SigningSpec).Range input × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support ((CappedExecution.cappedBothTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    traceActive secretKey.parameter result.2.2 =
      (traceActive secretKey.parameter state.2 || activity secretKey.parameter input) := by
  simp only [CappedExecution.cappedBothTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact traceActive_append_fragment _ _ _ _

theorem sourcePrefix_stopped_event_eq (adversary : Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (event : Forgery × CappedExecution.SourceExactTracedState → Prop)
    (hgate : ∀ result, event result → traceActive key.secretKey.parameter result.2.2 = true) :
    Pr[event | Deciding.sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[event | Deciding.sourcePrefixExecution adversary key] := by
  have hparameter : key.publicKey.parameter = key.secretKey.parameter :=
    CappedExecution.keygen_parameter_eq key.keyResult (CappedExecution.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
  have h := probEvent_stopInactive_eq
    (CappedExecution.cappedBothTracedMappedAdversaryImpl key.publicKey (Keygen.materializePrecomputation key.cache key.secretKey))
    (activity key.secretKey.parameter) (activity_charged key.secretKey.parameter)
    (fun state : CappedExecution.SourceExactTracedState => traceActive key.secretKey.parameter state.2)
    (by
      intro input state result hresult
      simpa only [Keygen.materializePrecomputation_parameter] using
        sourceExact_activity_step key.publicKey (Keygen.materializePrecomputation key.cache key.secretKey)
          input state result hresult)
    event hgate stoppedFallback (adversary.main key.publicKey) q ((((key.cache, []), []), []))
    (hbound key.publicKey)
  simpa only [Deciding.sourcePrefixExecution, stoppedAdversary, hparameter,
    show traceActive key.secretKey.parameter [] = false from rfl] using h

theorem sourcePrefix_stopped_freshFirstLane_eq (adversary : Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen) :
    Pr[FreshPrefixFirstLaneEvent key | Deciding.sourcePrefixExecution (stoppedAdversary q adversary) key] =
      Pr[FreshPrefixFirstLaneEvent key | Deciding.sourcePrefixExecution adversary key] := by
  let event := fun result : Forgery × CappedExecution.SourceExactTracedState =>
    FreshPrefixFirstLaneEvent key result ∧ traceActive key.secretKey.parameter result.2.2 = true
  have heq (adv : Adversary) :
      Pr[FreshPrefixFirstLaneEvent key | Deciding.sourcePrefixExecution adv key] =
        Pr[event | Deciding.sourcePrefixExecution adv key] := by
    apply probEvent_congr' (fun result hresult => ?_) rfl
    exact ⟨fun h => ⟨h, sourcePrefix_freshAccepted_active adv key hkey result hresult h.2⟩, And.left⟩
  rw [heq, heq]
  exact sourcePrefix_stopped_event_eq adversary q hbound key hkey event (fun _ h => h.2)

theorem sourcePrefixProgram_stopped_freshFirstLane_eq (adversary : Adversary) (q : ℕ)
    (hbound : IsQueryBound adversary q) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 |
      Deciding.sourcePrefixProgram (stoppedAdversary q adversary)] =
      Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Deciding.sourcePrefixProgram adversary] := by
  unfold Deciding.sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def]
    rw [sourcePrefix_stopped_freshFirstLane_eq adversary q hbound key hkey]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.sourcePrefixProgram_stopped_freshFirstLane_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_stopped_freshFirstLane_eq

end Xmss.TargetSum.EUFCMA.Requests

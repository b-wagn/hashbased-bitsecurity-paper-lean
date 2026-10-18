import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsTerminalCost
import XmssSecurity.Proof.TargetSum.EUFCMA.FreshExpectedPrefix
import XmssSecurity.Proof.TargetSum.ExpectedStateCounter

/-! Encoding queries and signing requests are the relevant prefix activity.
Their trace counter records every request, including unsuccessful signing. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

attribute [local irreducible] encodingInputLeafIndex?

def IsActivity (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) : Prop :=
  Direct.IsDirectEncodingQuery parameter input ∨ IsSigningRequest input

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsActivity parameter) :=
  fun input => inferInstanceAs
    (Decidable (Direct.IsDirectEncodingQuery parameter input ∨ IsSigningRequest input))

noncomputable def activity (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain) : Bool :=
  decide (IsActivity parameter input)

noncomputable def activityCount (parameter : PublicParameter) (trace : CappedChain.AttackerActionTrace) : ℕ :=
  CappedChain.AttackerActionTrace.encodingInputCount parameter trace +
    (CappedChain.AttackerActionTrace.toSigningLog trace).length

noncomputable def traceActive (parameter : PublicParameter) (trace : AttackerActionTrace) : Bool :=
  decide (0 < activityCount parameter trace)

theorem activity_charged (parameter : PublicParameter) (input : (OracleWorld + SigningSpec).Domain)
    (h : activity parameter input = true) : IsCharged input := by
  have hactivity : IsActivity parameter input := of_decide_eq_true h
  rcases input with (sample | hashInput) | request
  · exact hactivity.elim False.elim False.elim
  · rfl
  · rfl

theorem activityCount_append_fragment (parameter : PublicParameter) (trace : AttackerActionTrace)
    (input : (OracleWorld + SigningSpec).Domain) (answer : (OracleWorld + SigningSpec).Range input) :
    activityCount parameter (trace ++ attackerActionFragment input answer) =
      activityCount parameter trace + if IsActivity parameter input then 1 else 0 := by
  simp only [activityCount, AttackerActionTrace.encodingInputCount_append,
    attackerActionFragment_encodingInputCount, AttackerActionTrace.toSigningLog_append,
    attackerActionFragment_toSigningLog, List.length_append]
  rcases input with (sample | hashInput) | request
  · simp [IsActivity, Direct.IsDirectEncodingQuery, CappedEncodingMonitor.IsEncodingHashQuery,
      IsSigningRequest, signingLogFragment]
  · simp only [IsActivity, Direct.IsDirectEncodingQuery, CappedEncodingMonitor.IsEncodingHashQuery,
      IsSigningRequest, or_false, signingLogFragment,
      List.length_nil, Nat.add_zero]
    by_cases hencoding : (encodingInputLeafIndex? parameter hashInput).isSome = true
    · simp only [if_pos hencoding]; omega
    · simp only [if_neg hencoding]; omega
  · simp [IsActivity, Direct.IsDirectEncodingQuery, IsSigningRequest, signingLogFragment, Nat.add_assoc]

theorem traceActive_append_fragment (parameter : PublicParameter) (trace : AttackerActionTrace)
    (input : (OracleWorld + SigningSpec).Domain) (answer : (OracleWorld + SigningSpec).Range input) :
    traceActive parameter (trace ++ attackerActionFragment input answer) =
      (traceActive parameter trace || activity parameter input) := by
  simp only [traceActive, activityCount_append_fragment, activity]
  by_cases h : IsActivity parameter input <;> simp [h]

theorem expectedQueries_forget_trace (publicKey : PublicKey) (secretKey : SecretKey)
    (predicate : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred predicate]
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : AttackerActionTrace) :
    expectedSimulatedQueryCount (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      predicate computation (cache, trace) =
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
      predicate computation cache := by
  apply expectedSimulatedQueryCount_eq_of_query_map_eq
    (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (cappedUnloggedMappedAdversaryImpl publicKey secretKey) Prod.fst
  intro input state
  simp only [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
    map_bind, map_pure, Prod.map_apply, id_eq]
  change ((sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1 >>= pure) = _
  rw [bind_pure]
  cases input <;> rfl

theorem sourcePrefix_freshAccepted_active (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (result : Forgery × SourceExactTracedState) (hresult : result ∈ support (sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixFreshAccepted key result) : traceActive key.secretKey.parameter result.2.2 = true := by
  obtain ⟨encoding, hdecode⟩ := hfresh.2
  have hcached := CacheView.encodingInput_cached_of_decode_some result.2.1.1.1 key.secretKey.parameter
    result.1.epoch result.1.message result.1.signature.randomness encoding hdecode
  obtain ⟨output, houtput⟩ := hcached
  have hpositive := sourcePrefix_fresh_encoding_cached_positive_count adversary key hkey result hresult hfresh.1
    (by rw [houtput]; simp)
  apply decide_eq_true
  change 0 < CappedChain.AttackerActionTrace.encodingInputCount key.secretKey.parameter result.2.2 + _
  omega

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefix_freshAccepted_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_freshAccepted_active

end XmssSecurity.TargetSum.EUFCMA.Requests

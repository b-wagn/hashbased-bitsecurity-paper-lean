import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsTerminalCost
import XmssSecurity.Proof.TargetSum.EUFCMA.FreshExpectedPrefix
import XmssSecurity.Proof.TargetSum.ExpectedStateCounter
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.CacheDecode
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Encoding queries and signing requests are the relevant prefix activity.
Their trace counter records every request, including unsuccessful signing. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

attribute [local irreducible] Generic.encodingInputLeafIndex?

def IsActivity (parameter : PublicParameter) (input : (OracleWorld + Generic.SigningSpec).Domain) : Prop :=
  Generic.Direct.IsDirectEncodingQuery parameter input ∨ IsSigningRequest input

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsActivity parameter) :=
  fun input => inferInstanceAs
    (Decidable (Generic.Direct.IsDirectEncodingQuery parameter input ∨ IsSigningRequest input))

noncomputable def activity (parameter : PublicParameter) (input : (OracleWorld + Generic.SigningSpec).Domain) : Bool :=
  decide (IsActivity parameter input)

noncomputable def activityCount (parameter : PublicParameter) (trace : Generic.CappedChain.AttackerActionTrace) : ℕ :=
  Generic.CappedChain.AttackerActionTrace.encodingInputCount parameter trace +
    (Generic.CappedChain.AttackerActionTrace.toSigningLog trace).length

noncomputable def traceActive (parameter : PublicParameter) (trace : Generic.AttackerActionTrace) : Bool :=
  decide (0 < activityCount parameter trace)

theorem activity_charged (parameter : PublicParameter) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (h : activity parameter input = true) : IsCharged input := by
  have hactivity : IsActivity parameter input := of_decide_eq_true h
  rcases input with (sample | hashInput) | request
  · exact hactivity.elim False.elim False.elim
  · rfl
  · rfl

theorem activityCount_append_fragment (parameter : PublicParameter) (trace : Generic.AttackerActionTrace)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (answer : (OracleWorld + Generic.SigningSpec).Range input) :
    activityCount parameter (trace ++ Generic.CappedChain.attackerActionFragment input answer) =
      activityCount parameter trace + if IsActivity parameter input then 1 else 0 := by
  simp only [activityCount, Generic.CappedChain.AttackerActionTrace.encodingInputCount_append,
    attackerActionFragment_encodingInputCount, Generic.CappedChain.AttackerActionTrace.toSigningLog_append,
    Generic.CappedChain.attackerActionFragment_toSigningLog, List.length_append]
  rcases input with (sample | hashInput) | request
  · simp [IsActivity, Generic.Direct.IsDirectEncodingQuery, Generic.CappedEncodingMonitor.IsEncodingHashQuery,
      IsSigningRequest, Generic.signingLogFragment]
  · simp only [IsActivity, Generic.Direct.IsDirectEncodingQuery, Generic.CappedEncodingMonitor.IsEncodingHashQuery,
      IsSigningRequest, or_false, Generic.signingLogFragment,
      List.length_nil, Nat.add_zero]
    by_cases hencoding : (Generic.encodingInputLeafIndex? parameter hashInput).isSome = true
    · simp only [if_pos hencoding]; omega
    · simp only [if_neg hencoding]; omega
  · simp [IsActivity, Generic.Direct.IsDirectEncodingQuery, IsSigningRequest, Generic.signingLogFragment, Nat.add_assoc]

theorem traceActive_append_fragment (parameter : PublicParameter) (trace : Generic.AttackerActionTrace)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (answer : (OracleWorld + Generic.SigningSpec).Range input) :
    traceActive parameter (trace ++ Generic.CappedChain.attackerActionFragment input answer) =
      (traceActive parameter trace || activity parameter input) := by
  simp only [traceActive, activityCount_append_fragment, activity]
  by_cases h : IsActivity parameter input <;> simp [h]

theorem expectedQueries_forget_trace (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (predicate : (OracleWorld + Generic.SigningSpec).Domain → Prop) [DecidablePred predicate]
    {α : Type} (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (cache : QueryCache HashSpec) (trace : Generic.AttackerActionTrace) :
    expectedSimulatedQueryCount (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
      predicate computation (cache, trace) =
    expectedSimulatedQueryCount (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey)
      predicate computation cache := by
  apply expectedSimulatedQueryCount_eq_of_query_map_eq
    (Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (Generic.cappedUnloggedMappedAdversaryImpl publicKey secretKey) Prod.fst
  intro input state
  simp only [Generic.CappedChain.sourceDirectTracedMappedAdversaryImpl, Generic.CappedChain.actionTracedStateImpl, StateT.run_mk,
    map_bind, map_pure, Prod.map_apply, id_eq]
  change ((Generic.CappedChain.sourceDirectMappedAdversaryImpl publicKey secretKey input).run state.1 >>= pure) = _
  rw [bind_pure]
  cases input <;> rfl

theorem sourcePrefix_freshAccepted_active (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (result : Generic.Forgery × Generic.CappedChain.SourceExactTracedState) (hresult : result ∈ support (Generic.Deciding.sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixFreshAccepted key result) : traceActive key.secretKey.parameter result.2.2 = true := by
  obtain ⟨encoding, hdecode⟩ := hfresh.2
  have hcached := TargetSum.encodingInput_cached_of_decode_some result.2.1.1.1 key.secretKey.parameter
    result.1.epoch result.1.message result.1.signature.randomness encoding hdecode
  obtain ⟨output, houtput⟩ := hcached
  have hpositive := sourcePrefix_fresh_encoding_cached_positive_count adversary key hkey result hresult hfresh.1
    (by rw [houtput]; simp)
  apply decide_eq_true
  change 0 < Generic.CappedChain.AttackerActionTrace.encodingInputCount key.secretKey.parameter result.2.2 + _
  omega

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefix_freshAccepted_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_freshAccepted_active

end XmssSecurity.TargetSum.EUFCMA.Requests

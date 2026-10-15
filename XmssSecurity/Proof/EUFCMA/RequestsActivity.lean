import XmssSecurity.Proof.EUFCMA.RequestsTerminalCost
import XmssSecurity.Proof.EUFCMA.FreshExpectedPrefix
import XmssSecurity.Proof.ExpectedStateCounter

/-! Encoding queries and signing requests are the relevant prefix activity.
Their trace counter records every request, including unsuccessful signing. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.EUFCMA.Requests

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

theorem source_activityCount_step (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : SourceTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    activityCount secretKey.parameter result.2.2 = activityCount secretKey.parameter state.2 +
      if IsActivity secretKey.parameter input then 1 else 0 := by
  simp only [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact activityCount_append_fragment _ _ _ _

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

theorem source_activity_probability_le (publicKey : PublicKey) (secretKey : SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    Pr[fun result => traceActive secretKey.parameter result.2.2 = true |
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run (cache, [])] ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) computation cache +
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsSigningRequest computation cache := by
  have hcount := expectedStateCounter_eq_initial_add_queries (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    (IsActivity secretKey.parameter) (fun state => activityCount secretKey.parameter state.2)
    (source_activityCount_step publicKey secretKey) computation (cache, [])
  simp only [show activityCount secretKey.parameter [] = 0 from rfl, Nat.cast_zero, zero_add] at hcount
  rw [expectedQueries_forget_trace] at hcount
  have hdisjoint (input : (OracleWorld + SigningSpec).Domain) :
      ¬(Direct.IsDirectEncodingQuery secretKey.parameter input ∧ IsSigningRequest input) := by
    rcases input with (sample | hashInput) | request <;> simp [Direct.IsDirectEncodingQuery, IsSigningRequest]
  rw [← expectedSimulatedQueryCount_or_of_disjoint _ _ _ hdisjoint]
  unfold IsActivity at hcount
  rw [← hcount, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hactive
  · apply le_mul_of_one_le_right'
    have h : 0 < activityCount secretKey.parameter result.2.2 := of_decide_eq_true hactive
    exact_mod_cast h
  · exact zero_le

/-- info: 'XmssSecurity.EUFCMA.Requests.source_activity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_activity_probability_le

theorem sourcePrefix_activity_probability_le (adversary : XmssSecurity.Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    Pr[fun result => traceActive key.secretKey.parameter result.2.2 = true |
      sourcePrefixExecution adversary key] ≤
      expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl key.publicKey (materializePrecomputation key.cache key.secretKey))
        (Direct.IsDirectEncodingQuery key.secretKey.parameter) (adversary.main key.publicKey) key.cache +
      expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl key.publicKey (materializePrecomputation key.cache key.secretKey))
        IsSigningRequest (adversary.main key.publicKey) key.cache := by
  have h := source_activity_probability_le key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache
  rw [← cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((key.cache, []), []) [], probEvent_map] at h
  exact h

theorem sourcePrefixProgram_activity_probability_le (adversary : XmssSecurity.Adversary) :
    Pr[fun result => traceActive result.1.secretKey.parameter result.2.2.2 = true |
      sourcePrefixProgram adversary] ≤
      Direct.expectedDirectEncodingQueries adversary + expectedSigningRequests adversary := by
  let credit := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2 +
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      IsSigningRequest (adversary.main keyResult.1.1) keyResult.2
  have hmean : (∑' key, Pr[= key | trajectoryProgrammedGlobalChainKeygen] *
      credit (materializeCachedKeyResult key.keyResult)) =
        Direct.expectedDirectEncodingQueries adversary + expectedSigningRequests adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : ProgrammedGlobalChainKeygenView =>
          materializeCachedKeyResult key.keyResult) <$> trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] * credit keyResult := by
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
      _ = _ := by simp only [credit, mul_add, ENNReal.tsum_add]; rfl
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  simpa only [credit, materializeCachedKeyResult, ProgrammedGlobalChainKeygenView.keyResult,
    materializePrecomputation, precomputedSecretKey] using sourcePrefix_activity_probability_le adversary key

theorem sourcePrefix_freshAccepted_active (adversary : XmssSecurity.Adversary)
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

/-- info: 'XmssSecurity.EUFCMA.Requests.sourcePrefixProgram_activity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_activity_probability_le

/-- info: 'XmssSecurity.EUFCMA.Requests.sourcePrefix_freshAccepted_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefix_freshAccepted_active

end XmssSecurity.EUFCMA.Requests

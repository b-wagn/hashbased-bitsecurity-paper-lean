import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsActivity

/-! A nonempty signing transcript is paid for by the expected request count,
including requests that return no signature. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem signingCount_append_fragment (trace : CappedChain.AttackerActionTrace)
    (input : (OracleWorld + SigningSpec).Domain) (answer : (OracleWorld + SigningSpec).Range input) :
    (trace ++ attackerActionFragment input answer).toSigningLog.length =
      trace.toSigningLog.length + if IsSigningRequest input then 1 else 0 := by
  simp only [AttackerActionTrace.toSigningLog_append, attackerActionFragment_toSigningLog,
    List.length_append]
  rcases input with (sample | hashInput) | request <;> simp [IsSigningRequest, signingLogFragment]

theorem source_signingCount_step (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : SourceTracedState)
    (result : (OracleWorld + SigningSpec).Range input × SourceTracedState)
    (hresult : result ∈ support ((sourceDirectTracedMappedAdversaryImpl publicKey secretKey input).run state)) :
    result.2.2.toSigningLog.length = state.2.toSigningLog.length +
      if IsSigningRequest input then 1 else 0 := by
  simp only [sourceDirectTracedMappedAdversaryImpl, actionTracedStateImpl, StateT.run_mk,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  exact signingCount_append_fragment _ _ _

theorem source_signingActivity_probability_le (publicKey : PublicKey) (secretKey : SecretKey)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    Pr[fun result => 0 < result.2.2.toSigningLog.length |
      (simulateQ (sourceDirectTracedMappedAdversaryImpl publicKey secretKey) computation).run (cache, [])] ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsSigningRequest computation cache := by
  have hcount := expectedStateCounter_eq_initial_add_queries (sourceDirectTracedMappedAdversaryImpl publicKey secretKey)
    IsSigningRequest (fun state => state.2.toSigningLog.length)
    (source_signingCount_step publicKey secretKey) computation (cache, [])
  simp only [show CappedChain.AttackerActionTrace.toSigningLog [] = [] from rfl,
    List.length_nil, Nat.cast_zero, zero_add] at hcount
  rw [expectedQueries_forget_trace] at hcount
  rw [← hcount, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  split_ifs with hactive
  · apply le_mul_of_one_le_right'
    exact_mod_cast hactive
  · exact zero_le

theorem sourcePrefix_signingActivity_probability_le (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    Pr[fun result => 0 < result.2.2.toSigningLog.length | sourcePrefixExecution adversary key] ≤
      expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl key.publicKey (materializePrecomputation key.cache key.secretKey))
        IsSigningRequest (adversary.main key.publicKey) key.cache := by
  have h := source_signingActivity_probability_le key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) key.cache
  rw [← cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((key.cache, []), []) [], probEvent_map] at h
  exact h

theorem sourcePrefixProgram_signingActivity_probability_le (adversary : XmssSecurity.TargetSum.Adversary) :
    Pr[fun result => 0 < result.2.2.2.toSigningLog.length | sourcePrefixProgram adversary] ≤
      expectedSigningRequests adversary := by
  let credit := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      IsSigningRequest (adversary.main keyResult.1.1) keyResult.2
  have hmean : (∑' key, Pr[= key | trajectoryProgrammedGlobalChainKeygen] *
      credit (materializeCachedKeyResult key.keyResult)) = expectedSigningRequests adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : ProgrammedGlobalChainKeygenView =>
          materializeCachedKeyResult key.keyResult) <$> trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = _ := by
        unfold expectedSigningRequests
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
  unfold sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean]
  apply ENNReal.tsum_le_tsum
  intro key
  apply mul_le_mul' le_rfl
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  simpa only [credit, materializeCachedKeyResult, ProgrammedGlobalChainKeygenView.keyResult,
    materializePrecomputation, precomputedSecretKey] using sourcePrefix_signingActivity_probability_le adversary key

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.sourcePrefixProgram_signingActivity_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourcePrefixProgram_signingActivity_probability_le

end XmssSecurity.TargetSum.EUFCMA.Requests

import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.Generic.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Moving the verifier's encoding query into the prefix preserves structural cost.
Only a fresh query can create an accepted encoding in a rejecting prefix cache. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct

theorem hasAcceptedEncoding_randomOracle_probability_le (parameter : PublicParameter)
    (input : HashInput) (cache : QueryCache HashSpec) :
    Pr[fun result => HasAcceptedEncoding parameter result.2 | (randomOracle (spec := HashSpec) input).run cache] ≤
      (if HasAcceptedEncoding parameter cache then 1 else 0) +
        (if cache input = none then TargetSum.acceptanceProbability else 0) := by
  by_cases haccepted : HasAcceptedEncoding parameter cache
  · rw [if_pos haccepted]
    exact le_add_right probEvent_le_one
  rw [if_neg haccepted, zero_add]
  cases hcache : cache input with
  | none =>
      rw [if_pos rfl]
      apply (hasAcceptedEncoding_romImpl_step_le parameter (.inr input) cache haccepted).trans
      split_ifs <;> first | exact le_rfl | exact zero_le
  | some output =>
      rw [if_neg (by simp), QueryImpl.withCaching_run_some _ hcache]
      simp [haccepted]

theorem adversaryPhase_withForgedEncodingQuery_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) :
    Deciding.adversaryPhase (Direct.withForgedEncodingQuery adversary) publicKey secretKey =
      (do
        let result ← Deciding.adversaryPhase adversary publicKey secretKey
        let _ ← liftM (OracleWorld.query (.inr (Direct.forgeryEncodingInput publicKey result.1)))
        pure result) :=
  Direct.run_simulateQ_withForgedEncodingQuery adversary secretKey publicKey

theorem expectedStructuralQueries_withForgedEncodingQuery_eq (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (hparameter : publicKey.parameter = secretKey.parameter)
    (targetCache initialCache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput secretKey targetCache input ≠ input)
      (Deciding.adversaryPhase (Direct.withForgedEncodingQuery adversary) publicKey secretKey) initialCache =
    expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput secretKey targetCache input ≠ input)
      (Deciding.adversaryPhase adversary publicKey secretKey) initialCache := by
  rw [adversaryPhase_withForgedEncodingQuery_eq, expectedSimulatedQueryCount_bind]
  have htail (result : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec) :
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput secretKey targetCache input ≠ input)
        (liftM (OracleWorld.query (.inr (Direct.forgeryEncodingInput publicKey result.1.1))) >>=
          fun _ => pure result.1) result.2 = 0 := by
    rw [expectedSimulatedQueryCount_query_bind]
    simp [Direct.forgeryEncodingInput, hparameter, Rom.IsRelevantHashQuery,
      keygenStructuralTargetInput_encodingInput]
  simp_rw [htail, mul_zero]
  rw [tsum_zero, add_zero]

theorem acceptedPrefix_withForgedEncodingQuery_probability_le (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (initialCache : QueryCache HashSpec) :
    Pr[fun result => HasAcceptedEncoding secretKey.parameter result.2 |
      (simulateQ romImpl (Deciding.adversaryPhase (Direct.withForgedEncodingQuery adversary) publicKey secretKey)).run
        initialCache] ≤
      Pr[fun result => HasAcceptedEncoding secretKey.parameter result.2 |
        (simulateQ romImpl (Deciding.adversaryPhase adversary publicKey secretKey)).run initialCache] +
      TargetSum.acceptanceProbability * Pr[fun result =>
        result.2 (Direct.forgeryEncodingInput publicKey result.1.1) = none |
        (simulateQ romImpl (Deciding.adversaryPhase adversary publicKey secretKey)).run initialCache] := by
  rw [adversaryPhase_withForgedEncodingQuery_eq, simulateQ_bind, StateT.run_bind,
    probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, probEvent_map]
  have h := mul_le_mul' (le_refl (Pr[= result |
      (simulateQ romImpl (Deciding.adversaryPhase adversary publicKey secretKey)).run initialCache]))
    (hasAcceptedEncoding_randomOracle_probability_le secretKey.parameter
      (Direct.forgeryEncodingInput publicKey result.1.1) result.2)
  apply h.trans_eq
  rw [mul_add]
  congr 1
  · split_ifs <;> simp only [mul_one, mul_zero]
  · split_ifs <;> simp only [mul_zero, zero_mul, mul_comm]

theorem acceptedPrefix_withForgedEncodingQuery_probability_le_expected (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (initialCache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding secretKey.parameter initialCache) :
    Pr[fun result => HasAcceptedEncoding secretKey.parameter result.2 |
      (simulateQ romImpl (Deciding.adversaryPhase (Direct.withForgedEncodingQuery adversary) publicKey secretKey)).run
        initialCache] ≤
      TargetSum.acceptanceProbability *
        (expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          (Deciding.adversaryPhase adversary publicKey secretKey) initialCache +
        Pr[fun result => result.2 (Direct.forgeryEncodingInput publicKey result.1.1) = none |
          (simulateQ romImpl (Deciding.adversaryPhase adversary publicKey secretKey)).run initialCache]) := by
  rw [mul_add]
  exact (acceptedPrefix_withForgedEncodingQuery_probability_le adversary publicKey secretKey initialCache).trans
    (add_le_add (probEvent_hasAcceptedEncoding_le_expectedQueries _ _ _ hcache) le_rfl)

/-- info: 'XmssSecurity.TargetSum.Direct.acceptedPrefix_withForgedEncodingQuery_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedPrefix_withForgedEncodingQuery_probability_le_expected

/-- info: 'XmssSecurity.TargetSum.Direct.expectedStructuralQueries_withForgedEncodingQuery_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedStructuralQueries_withForgedEncodingQuery_eq

end XmssSecurity.TargetSum.Direct

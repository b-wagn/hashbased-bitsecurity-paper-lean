import XmssSecurity.Proof.TargetSum.ExpectedCountedQueries
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing

/-! Every seeded signing attempt pairs one derivation hash with one encoding hash. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem randomizerHashInput_not_encoding (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    ¬CappedEncodingMonitor.IsEncodingHashQuery parameter
      (.inr (randomizerHashInput parameter seed leafIndex message trial)) := by
  intro hencoding
  change (encodingInputLeafIndex? parameter
    (randomizerHashInput parameter seed leafIndex message trial)).isSome at hencoding
  cases hleaf : encodingInputLeafIndex? parameter
      (randomizerHashInput parameter seed leafIndex message trial) with
  | none => simp [hleaf] at hencoding
  | some found =>
      obtain ⟨payload, hinput⟩ := exists_encodingInput_of_encodingInputLeafIndex?_eq_some
        parameter _ found hleaf
      have hseed := maySeedHit_randomizerHashInput parameter seed leafIndex message trial
      rw [← hinput] at hseed
      exact not_maySeedHit_tweakableHashInput parameter (.encoding found)
        (Concrete.encodingPayload payload.1 payload.2) hseed

theorem expectedQueries_deriveRandomizer
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate
      (deriveRandomizer parameter seed leafIndex message trial : OracleComp OracleWorld Randomness)
      cache = if predicate (.inr (randomizerHashInput parameter seed leafIndex message trial))
        then 1 else 0 := by
  change expectedSimulatedQueryCount romImpl predicate
    (liftM (OracleWorld.query (.inr (randomizerHashInput parameter seed leafIndex message trial))) >>=
      fun output => pure (output.extractLsb' 0 randomnessBits)) cache = _
  simp only [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_pure,
    mul_zero, tsum_zero, add_zero]

theorem expectedQueries_precomputedSignAttempt
    (predicate : OracleWorld.Domain → Prop) [DecidablePred predicate]
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl predicate
      (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp OracleWorld (Option Signature)) cache =
      if predicate (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness))) then 1 else 0 := by
  rw [Concrete.precomputedSignAttempt, expectedSimulatedQueryCount_bind]
  calc
    _ = expectedSimulatedQueryCount romImpl predicate
        (Concrete.encodingHash secretKey.parameter leafIndex message randomness) cache + 0 := by
      congr 1
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      cases TargetSum.decodeDigest result.1 <;>
        simp only [expectedSimulatedQueryCount_pure, mul_zero]
    _ = _ := by
      rw [add_zero]
      change expectedSimulatedQueryCount romImpl predicate
        (liftM (OracleWorld.query (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, randomness)))) >>= fun output => pure (truncateHash output)) cache = _
      simp only [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_pure,
        mul_zero, tsum_zero, add_zero]

theorem expected_const_add_mul_eq (computation : ProbComp α)
    (constant rate : ℝ≥0∞) (cost : α → ℝ≥0∞) :
    (∑' result, Pr[= result | computation] * (constant + rate * cost result)) =
      constant + rate * ∑' result, Pr[= result | computation] * cost result := by
  simp_rw [mul_add, mul_left_comm (Pr[= _ | computation]) rate]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
    tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

theorem Seeded.expected_signFrom_hashQueries_eq_twice_encodingQueries
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (attempts trial : ℕ) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl IsHashQuery
      (signFrom secretKey leafIndex message attempts trial : OracleComp OracleWorld (Option Signature))
      cache =
      2 * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery secretKey.precomputed.parameter)
        (signFrom secretKey leafIndex message attempts trial : OracleComp OracleWorld (Option Signature))
        cache := by
  induction attempts generalizing trial cache with
  | zero => simp [signFrom]
  | succ attempts ih =>
      let enc := CappedEncodingMonitor.IsEncodingHashQuery secretKey.precomputed.parameter
      let continuation : Option Signature → OracleComp OracleWorld (Option Signature) := fun answer =>
        match answer with
        | some signature => pure (some signature)
        | none => signFrom secretKey leafIndex message attempts (trial + 1)
      let weight := fun result : Randomness × QueryCache HashSpec =>
        ∑' answer, Pr[= answer | (simulateQ romImpl
          (Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message result.1 :
            OracleComp OracleWorld (Option Signature))).run result.2] *
          expectedSimulatedQueryCount romImpl enc (continuation answer.1) answer.2
      let derivation := (simulateQ romImpl
        (deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message
          (BitVec.ofNat 32 trial) : OracleComp OracleWorld Randomness)).run cache
      simp only [signFrom, expectedSimulatedQueryCount_bind, expectedQueries_deriveRandomizer,
        randomizerHashInput_not_encoding, if_false, zero_add]
      simp only [expectedQueries_precomputedSignAttempt]
      simp only [IsHashQuery, if_true, CappedEncodingMonitor.IsEncodingHashQuery_inr,
        encodingInputLeafIndex?_encodingInput, Option.isSome_some, if_true]
      calc
        _ = 1 + ∑' result, Pr[= result | derivation] * (1 + 2 * weight result) := by
          congr 1
          apply tsum_congr
          intro result
          congr 1
          congr 1
          rw [show weight result = _ from rfl, ← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro answer
          rw [mul_left_comm]
          congr 1
          cases answer.1 with
          | none => exact ih (trial + 1) answer.2
          | some signature => simp [continuation]
        _ = 2 * ∑' result, Pr[= result | derivation] * (1 + weight result) := by
          rw [expected_const_add_mul_eq]
          have hunit : (∑' result, Pr[= result | derivation] * (1 + weight result)) =
              1 + ∑' result, Pr[= result | derivation] * weight result := by
            simpa only [one_mul] using expected_const_add_mul_eq derivation 1 1 weight
          rw [hunit]
          ring
        _ = _ := rfl

theorem deriveRandomizer_lift_hash_eq_world
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) :
    (liftM (deriveRandomizer parameter seed leafIndex message trial : OracleComp HashSpec Randomness) :
      OracleComp OracleWorld Randomness) = deriveRandomizer parameter seed leafIndex message trial := by
  simp only [deriveRandomizer, Concrete.oracleHash, liftM_bind, liftM_pure]
  rfl

theorem Concrete.precomputedSignAttempt_lift_hash_eq_world
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    (liftM (precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      precomputedSignAttempt secretKey leafIndex message randomness := by
  have hencoding : (liftM (encodingHash secretKey.parameter leafIndex message randomness :
      OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) =
      encodingHash secretKey.parameter leafIndex message randomness := by
    simp only [encodingHash, tweakableHash, oracleHash, liftM_bind, liftM_pure]
    rfl
  rw [precomputedSignAttempt, liftM_bind, hencoding, precomputedSignAttempt]
  apply bind_congr
  intro digest
  cases TargetSum.decodeDigest digest <;> simp only [liftM_pure]

theorem Seeded.signFrom_lift_hash_eq_world
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (attempts trial : ℕ) :
    (liftM (signFrom secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      signFrom secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [signFrom]
  | succ attempts ih =>
      simp only [signFrom, liftM_bind, deriveRandomizer_lift_hash_eq_world,
        Concrete.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro randomness
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

theorem xmss_sign_expected_hashQueries_eq_twice_encodingQueries
    (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl IsHashQuery (xmss.sign secretKey leafIndex message) cache =
      2 * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery secretKey.precomputed.parameter)
        (xmss.sign secretKey leafIndex message) cache := by
  change expectedSimulatedQueryCount romImpl IsHashQuery
      (liftM (Seeded.signFrom secretKey leafIndex message signingAttemptLimit 0 :
        OracleComp HashSpec (Option Signature))) cache = _
  simp only [xmss, Seeded.sign, Seeded.signFrom_lift_hash_eq_world]
  exact Seeded.expected_signFrom_hashQueries_eq_twice_encodingQueries _ _ _ _ _ _

/-- info: 'XmssSecurity.TargetSum.xmss_sign_expected_hashQueries_eq_twice_encodingQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sign_expected_hashQueries_eq_twice_encodingQueries

end XmssSecurity.TargetSum

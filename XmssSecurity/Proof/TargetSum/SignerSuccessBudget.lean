import XmssSecurity.Proof.TargetSum.SignerEncodingCost

/-! A successful seeded signing call must have paid for an accepted encoding. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem Concrete.precomputedSignAttempt_replay_success_hasAcceptedEncoding
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (signature : Signature)
    (heval : evalWithAnswerFn (CacheReplay.answerFn cache)
      (precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature)) = some signature) :
    HasAcceptedEncoding secretKey.parameter cache := by
  unfold precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, CacheReplay.eval_encodingHash] at heval
  cases hdecode : TargetSum.decodeDigest
      (CacheView.encodingHash cache secretKey.parameter leafIndex (message, randomness)) with
  | none => simp [hdecode, evalWithAnswerFn_pure] at heval
  | some encoding => exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode

theorem Seeded.signFrom_replay_success_hasAcceptedEncoding
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (attempts trial : ℕ) (cache : QueryCache HashSpec) (signature : Signature)
    (heval : evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (signFrom secretKey leafIndex message attempts trial : OracleComp HashSpec (Option Signature)) =
        some signature) : HasAcceptedEncoding secretKey.precomputed.parameter cache := by
  induction attempts generalizing trial with
  | zero => simp [signFrom, evalWithAnswerFn_pure] at heval
  | succ attempts ih =>
      simp only [signFrom, evalWithAnswerFn_bind] at heval
      split at heval
      · rename_i returned hreturned
        exact Concrete.precomputedSignAttempt_replay_success_hasAcceptedEncoding
          _ _ _ _ _ returned hreturned
      · exact ih (trial + 1) heval

theorem Seeded.signFrom_hasAcceptedEncoding_of_success
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (attempts trial : ℕ) (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support ((simulateQ randomOracle
      (signFrom secretKey leafIndex message attempts trial : OracleComp HashSpec (Option Signature))).run
        initialCache)) : HasAcceptedEncoding secretKey.precomputed.parameter finalCache := by
  exact signFrom_replay_success_hasAcceptedEncoding _ _ _ _ _ _ signature
    (Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support _ _ _ _ hmem)

theorem xmss_sign_hasAcceptedEncoding_of_success
    (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (xmss.sign secretKey leafIndex message)).run initialCache)) :
    HasAcceptedEncoding secretKey.precomputed.parameter finalCache := by
  have hroute : simulateQ romImpl (xmss.sign secretKey leafIndex message) =
      simulateQ randomOracle
        (Seeded.signFrom secretKey leafIndex message signingAttemptLimit 0 :
          OracleComp HashSpec (Option Signature)) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
      (liftM (Seeded.signFrom secretKey leafIndex message signingAttemptLimit 0 :
        OracleComp HashSpec (Option Signature))) = _
    exact QueryImpl.simulateQ_add_liftM_right _ _ _
  rw [hroute] at hmem
  exact Seeded.signFrom_hasAcceptedEncoding_of_success _ _ _ _ _ _ _ signature hmem

/-- Even an early successful call pays for its success in expectation. The premise allows
arbitrary previously cached rejected encodings and derivation inputs. -/
theorem xmss_sign_success_le_half_expectedHashQueries
    (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) (hcache : ¬HasAcceptedEncoding secretKey.precomputed.parameter cache) :
    Pr[fun result : Option Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (xmss.sign secretKey leafIndex message)).run cache] ≤
      (TargetSum.acceptanceProbability / 2) * expectedSimulatedQueryCount romImpl IsHashQuery
        (xmss.sign secretKey leafIndex message) cache := by
  calc
    _ ≤ Pr[fun result => HasAcceptedEncoding secretKey.precomputed.parameter result.2 |
        (simulateQ romImpl (xmss.sign secretKey leafIndex message)).run cache] := by
      apply probEvent_mono
      rintro ⟨answer, finalCache⟩ hresult hsuccess
      cases answer with
      | none => exact (hsuccess rfl).elim
      | some signature =>
          exact xmss_sign_hasAcceptedEncoding_of_success _ _ _ _ _ signature hresult
    _ ≤ TargetSum.acceptanceProbability * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery secretKey.precomputed.parameter)
        (xmss.sign secretKey leafIndex message) cache :=
      probEvent_hasAcceptedEncoding_le_expectedQueries _ _ _ hcache
    _ = _ := by
      rw [xmss_sign_expected_hashQueries_eq_twice_encodingQueries, ← mul_assoc]
      congr 1
      exact (ENNReal.div_mul_cancel (by norm_num) (by norm_num)).symm

/-- info: 'XmssSecurity.TargetSum.xmss_sign_success_le_half_expectedHashQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sign_success_le_half_expectedHashQueries

end XmssSecurity.TargetSum

import XmssSecurity.Proof.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.EncodingAcceptanceBudget

/-! A fresh verification encoding is accepted with its ordinary sampling probability.
The same bound applies when the entire prefix cache contains no accepted encoding. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Direct

theorem verifyAfterDigest_eq_false_of_invalid (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (digest : Digest) (hinvalid : ¬Checksum.ValidDigest digest) :
    verifyAfterDigest publicKey leafIndex signature digest = pure false := by
  unfold verifyAfterDigest
  cases hdecode : Checksum.decodeDigest digest with
  | none => rfl
  | some encoding => exact (hinvalid ⟨encoding, hdecode⟩).elim

theorem uniformValidHashOutput_bind_probability_le {α : Type}
    (continuation : HashOutput → ProbComp α) (event : α → Prop) (bound : ℝ≥0∞)
    (hvalid : ∀ output, Checksum.ValidDigest (truncateHash output) → Pr[event | continuation output] ≤ bound)
    (hinvalid : ∀ output, ¬Checksum.ValidDigest (truncateHash output) → Pr[event | continuation output] = 0) :
    Pr[event | ($ᵗ HashOutput) >>= continuation] ≤ Checksum.acceptanceProbability * bound := by
  classical
  rw [probEvent_bind_eq_tsum, ← Checksum.probEvent_validDigest_uniformHashOutput,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro output
  by_cases houtput : Checksum.ValidDigest (truncateHash output)
  · simp only [houtput, if_true]
    exact mul_le_mul' le_rfl (hvalid output houtput)
  · simp only [houtput, if_false, hinvalid output houtput, mul_zero, zero_mul, le_refl]

theorem verify_run_fresh (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    (simulateQ romImpl (Concrete.scheme.verify publicKey leafIndex message signature)).run cache = (do
      let output ← ($ᵗ HashOutput)
      (simulateQ randomOracle (verifyAfterDigest publicKey leafIndex signature (truncateHash output))).run
        (cache.cacheQuery (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
          (message, signature.randomness)) output)) := by
  rw [simulateQ_romImpl_scheme_verify, StateT.run_bind,
    randomOracle_run_none_eq_uniformHashOutput _ _ hfresh, bind_map_left]
  rfl

theorem verify_probability_le_acceptance_of_fresh (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    Pr[fun result => result.1 = true |
      (simulateQ romImpl (Concrete.scheme.verify publicKey leafIndex message signature)).run cache] ≤
      Checksum.acceptanceProbability := by
  rw [verify_run_fresh publicKey leafIndex message signature cache hfresh]
  simpa only [mul_one] using uniformValidHashOutput_bind_probability_le _
    (fun result : Bool × QueryCache HashSpec => result.1 = true) 1
    (fun _ _ => probEvent_le_one) (fun output hinvalid => by
      rw [verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
      simp)

theorem verify_probability_eq_zero_of_cached_invalid (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (cache : QueryCache HashSpec) (output : HashOutput)
    (hcached : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = some output)
    (hinvalid : ¬Checksum.ValidDigest (truncateHash output)) :
    Pr[fun result => result.1 = true |
      (simulateQ romImpl (Concrete.scheme.verify publicKey leafIndex message signature)).run cache] = 0 := by
  rw [simulateQ_romImpl_scheme_verify, StateT.run_bind, QueryImpl.withCaching_run_some _ hcached,
    pure_bind, verifyAfterDigest_eq_false_of_invalid _ _ _ _ hinvalid]
  simp

theorem verify_probability_le_acceptance_of_noAcceptedEncoding (publicKey : PublicKey)
    (leafIndex : LeafIndex) (message : Message) (signature : Signature) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding publicKey.parameter cache) :
    Pr[fun result => result.1 = true |
      (simulateQ romImpl (Concrete.scheme.verify publicKey leafIndex message signature)).run cache] ≤
      Checksum.acceptanceProbability := by
  cases hentry : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) with
  | none => exact verify_probability_le_acceptance_of_fresh _ _ _ _ _ hentry
  | some output =>
      rw [verify_probability_eq_zero_of_cached_invalid _ _ _ _ _ output hentry (fun hvalid =>
        hcache ⟨_, output, hentry, by simp, hvalid⟩)]
      exact zero_le

/-- The acceptance factor remains valid after arbitrary prefix randomness and any
prefix event; the selected prefixes need only have no accepted encoding in their cache. -/
theorem verification_prefix_event_probability_le {α : Type}
    (head : ProbComp α) (publicKey : α → PublicKey) (forgery : α → Forgery)
    (cache : α → QueryCache HashSpec) (event : α → Prop)
    (hrejecting : ∀ result ∈ support head, event result → ¬HasAcceptedEncoding (publicKey result).parameter (cache result)) :
    Pr[fun result : α × (Bool × QueryCache HashSpec) => event result.1 ∧ result.2.1 = true | do
      let result ← head
      let verified ← (simulateQ romImpl (Concrete.scheme.verify (publicKey result)
        (forgery result).epoch (forgery result).message (forgery result).signature)).run (cache result)
      pure (result, verified)] ≤ Checksum.acceptanceProbability * Pr[event | head] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  simp only [bind_pure_comp, probEvent_map]
  by_cases hresult : result ∈ support head
  · by_cases hevent : event result
    · simp only [hevent, if_true, Function.comp_def, true_and]
      rw [mul_comm Checksum.acceptanceProbability]
      exact mul_le_mul' le_rfl (verify_probability_le_acceptance_of_noAcceptedEncoding _ _ _ _ _
        (hrejecting result hresult hevent))
    · simp only [Function.comp_def, hevent, false_and, if_false, mul_zero]
      rw [probEvent_eq_zero (fun _ _ h => h), mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hresult]
    simp

/-- info: 'XmssSecurity.Direct.verification_prefix_event_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verification_prefix_event_probability_le

end XmssSecurity.Direct

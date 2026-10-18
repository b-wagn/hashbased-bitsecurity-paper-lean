import XmssSecurity.Proof.TargetSum.EUFCMA.RootCollision
import XmssSecurity.Proof.TargetSum.Attack.EncodingNeighbors
import XmssSecurity.Proof.Generic.EncodingRejectionProbability
import XmssSecurity.Proof.Generic.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Reusing an honest signature for a fresh encoding can succeed through either
the original encoding or the final root comparison. The two contributions are
disjoint and both matter at a one-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Attack

theorem verifyReplay_run
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) (encoding : Encoding) (randomness : Randomness)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hdecode : Code.decodeDigest (Concrete.CacheView.encodingHash cache keyResult.1.2.parameter
      leafIndex (message, randomness)) = some encoding) :
    (simulateQ randomOracle (Generic.Concrete.verify keyResult.1.1 leafIndex message
      (Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding) :
        OracleComp HashSpec Bool)).run cache = pure (true, cache) := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let original := Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding
  have hreplace : CappedChain.replaceSignatureChainValue original chain (original.chainValue chain) = original := by
    simp [CappedChain.replaceSignatureChainValue]
    rfl
  have hverify := Attack.verifyMutatedSignature_run keyResult hkey leafIndex chain message encoding randomness
    (original.chainValue chain) cache hle
    (TargetSum.decodedEncoding_of_decodeDigest hdecode)
  rw [hreplace] at hverify
  rw [hverify, Attack.mutationRoot_eq_hashPath]
  have hpath := Attack.hashPath_run_honest
    (Attack.mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
    (Attack.mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain))
    0 (Attack.mutationChainSteps (encoding chain) + 1 + treeHeight) cache (by
      intro i _ hi
      obtain ⟨output, hcached, hnext⟩ := Attack.mutationReplayInputs_honest keyResult hkey leafIndex chain
        encoding randomness i (by omega)
      exact ⟨output, hle hcached, hnext⟩)
  simp only [Nat.zero_add] at hpath
  rw [Attack.mutationHonestValue_start _ _ _ _ _ randomness,
    Attack.mutationHonestValue_root keyResult hkey, Attack.mutationPath_length] at hpath
  dsimp only [Attack.mutationReplayInputs] at hpath
  dsimp only [original]
  rw [hpath]
  simp

noncomputable def digestCollisionRate : ℝ≥0∞ := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹

noncomputable def replayCollisionRate : ℝ≥0∞ :=
  TargetSum.acceptanceProbability * digestCollisionRate +
    digestCollisionRate * (1 - digestCollisionRate)

noncomputable def replayScore (target : Digest) (output : Digest) : ℝ≥0∞ :=
  (if Code.ValidDigest (output) then digestCollisionRate else 0) +
    (if output = target then 1 - digestCollisionRate else 0)

theorem digestCollisionRate_le_one : digestCollisionRate ≤ 1 := by
  norm_num [digestCollisionRate, digestBits]

theorem replayScore_average (target : Digest) :
    (∑' output, Pr[= output | $ᵗ Digest] * replayScore target output) = replayCollisionRate := by
  classical
  have hindicator (predicate : Digest → Prop) [DecidablePred predicate] (rate : ℝ≥0∞) :
      (∑' output, Pr[= output | $ᵗ Digest] * (if predicate output then rate else 0)) =
        Pr[predicate | $ᵗ Digest] * rate := by
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro output
    split <;> simp only [*, mul_zero, zero_mul]
  have hvalid : Pr[fun output : Digest => Code.ValidDigest (output) |
      $ᵗ Digest] = TargetSum.acceptanceProbability := by
    change Pr[Code.ValidDigest | $ᵗ Digest] = _
    exact TargetSum.probEvent_validDigest_uniform
  have heq : Pr[fun output : Digest => output = target | $ᵗ Digest] =
      digestCollisionRate := Rom.uniform_eq_probability target
  unfold replayScore
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, hindicator, hindicator, hvalid, heq]
  rfl

theorem replayScore_le_cached_verification
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) (encoding : Encoding) (hvalid : Code.Valid encoding)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hroot : RootCache keyResult.1.2.parameter leafIndex keyResult.1.1.root cache)
    (hfresh : cache (Concrete.CacheView.encodingInput keyResult.1.2.parameter leafIndex (message, randomness)) = none)
    (output : Digest) :
    replayScore (digestOfEncoding encoding) output ≤
      Pr[fun result : Bool × QueryCache HashSpec => result.1 = true |
        (simulateQ randomOracle (Generic.Concrete.verify keyResult.1.1 leafIndex message
          (Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding) :
            OracleComp HashSpec Bool)).run
              (cache.cacheQuery (Concrete.CacheView.encodingInput keyResult.1.2.parameter leafIndex
                (message, randomness)) output)] := by
  classical
  let updated := cache.cacheQuery (Concrete.CacheView.encodingInput keyResult.1.2.parameter leafIndex
    (message, randomness)) output
  have hcached : Concrete.CacheView.encodingHash updated keyResult.1.2.parameter leafIndex (message, randomness) =
      output := by simp [updated, Concrete.CacheView.encodingHash, Concrete.CacheView.digestAt]
  by_cases heq : output = digestOfEncoding encoding
  · have hdecode : Code.decodeDigest (Concrete.CacheView.encodingHash updated keyResult.1.2.parameter
        leafIndex (message, randomness)) = some encoding := by
      rw [hcached, heq]
      exact digestOfEncoding_decode encoding hvalid
    have hle' : keyResult.2 ≤ updated := hle.trans (QueryCache.le_cacheQuery cache hfresh)
    rw [verifyReplay_run keyResult hkey leafIndex message encoding randomness updated hle' hdecode]
    have hv : Code.ValidDigest (output) := by
      rw [Code.ValidDigest, heq, digestOfEncoding_decode encoding hvalid]
      simp
    simp only [replayScore, if_pos hv, if_pos heq,
      add_tsub_cancel_of_le digestCollisionRate_le_one, probEvent_pure, if_true, le_refl]
  · unfold replayScore
    rw [if_neg heq, add_zero]
    split
    · rename_i haccepted
      obtain ⟨acceptedEncoding, hdecode⟩ := haccepted
      apply verify_cached_encoding_probability_ge (encoding := acceptedEncoding)
      · rw [Deciding.keygen_publicKey_parameter_eq keyResult hkey]
        exact rootCache_cache_encoding _ _ _ _ hroot _ _ _ output
      · rw [Deciding.keygen_publicKey_parameter_eq keyResult hkey]
        change Code.decodeDigest (Concrete.CacheView.encodingHash updated keyResult.1.2.parameter
          leafIndex (message, randomness)) = some acceptedEncoding
        rwa [hcached]
    · exact zero_le

theorem verify_fresh_run (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Generic.Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    (simulateQ randomOracle (Generic.Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run cache =
      ($ᵗ Digest) >>= fun output =>
        (simulateQ randomOracle (Generic.Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run
          (cache.cacheQuery (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
            (message, signature.randomness)) output) := by
  conv_lhs => rw [Direct.concrete_verify_eq_query_bind, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, randomOracle_run_none_eq_uniformHashOutput _ _ hfresh,
    uniformHashOutput, bind_map_left]
  apply bind_congr
  intro output
  rw [Direct.concrete_verify_eq_query_bind, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]

theorem verify_fresh_replay_probability_ge
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) (encoding : Encoding) (hvalid : Code.Valid encoding)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hroot : RootCache keyResult.1.2.parameter leafIndex keyResult.1.1.root cache)
    (hfresh : cache (Concrete.CacheView.encodingInput keyResult.1.2.parameter leafIndex (message, randomness)) = none) :
    replayCollisionRate ≤
      Pr[fun result : Bool × QueryCache HashSpec => result.1 = true |
        (simulateQ randomOracle (Generic.Concrete.verify keyResult.1.1 leafIndex message
          (Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding) :
            OracleComp HashSpec Bool)).run cache] := by
  have hparameter := Deciding.keygen_publicKey_parameter_eq keyResult hkey
  rw [verify_fresh_run _ _ _ _ _ (by change cache (Concrete.CacheView.encodingInput keyResult.1.1.parameter
    leafIndex (message, randomness)) = none; rwa [hparameter]), probEvent_bind_eq_tsum,
    ← replayScore_average (digestOfEncoding encoding)]
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  rw [hparameter]
  exact replayScore_le_cached_verification keyResult hkey leafIndex message encoding hvalid randomness
    cache hle hroot hfresh output

/-- info: 'XmssSecurity.TargetSum.EUFCMA.verifyReplay_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyReplay_run

/-- info: 'XmssSecurity.TargetSum.EUFCMA.verify_fresh_replay_probability_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verify_fresh_replay_probability_ge

end XmssSecurity.TargetSum.EUFCMA

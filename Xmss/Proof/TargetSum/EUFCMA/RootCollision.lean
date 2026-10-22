import Xmss.Proof.Generic.Attack.MutationVerification
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.CacheDecode
import Xmss.Proof.TargetSum.EncodingProbability
/-! A lower bound for the final root comparison. If the root address contains
only answers with the public root digest, every final hash either reuses such an
answer or samples a fresh digest. Earlier verification steps avoid that address. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing

attribute [local irreducible] Generic.Verify.authenticationRoot

def finalRootLevel : MerkleLevel := ⟨31, by decide⟩

def finalRootDomain (leafIndex : LeafIndex) : Generic.HashDomain :=
  .merkle finalRootLevel (Generic.Merkle.nodeIndex leafIndex finalRootLevel.val)

def RootCache (parameter : PublicParameter) (leafIndex : LeafIndex)
    (root : Digest) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, AtHashAddress parameter (finalRootDomain leafIndex) input →
    cache input = some output → output = root

theorem rootCache_after_keygen
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (leafIndex : LeafIndex) :
    RootCache keyResult.1.2.parameter leafIndex keyResult.1.1.root keyResult.2 := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let encoding : Encoding := fun _ => ⟨0, by decide⟩
  let position := Attack.mutationChainSteps (encoding chain) + 1 + 31
  obtain ⟨answer, hcached, hnext⟩ := Attack.mutationReplayInputs_honest keyResult hkey
    leafIndex chain encoding chain position (by dsimp [position]; simp only [treeHeight]; omega)
  have hroot : Attack.mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain)
      (position + 1) = keyResult.1.1.root := by
    convert Attack.mutationHonestValue_root keyResult hkey leafIndex chain (encoding chain) using 1
    simp [position, treeHeight, Nat.add_assoc]
  rw [hroot] at hnext
  intro input output haddress houtput
  have hhonestAddress : AtHashAddress keyResult.1.2.parameter (finalRootDomain leafIndex)
      (Attack.mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding chain position
        (Attack.mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain) position)) := by
    unfold Attack.mutationReplayInputs position
    rw [Attack.mutationPathInput_node _ _ _ _ _ _ _ (by decide : 31 < treeHeight)]
    simp [CacheView.nodeInput, finalRootDomain, finalRootLevel]
  have heq := Keygen.keygen_cache_unique_merkleAddress _
    (Keygen.precomputedKeygen_support_oldKeygen keyResult hkey) finalRootLevel
    (Generic.Merkle.nodeIndex leafIndex finalRootLevel.val) _ _ output answer haddress hhonestAddress houtput hcached
  rw [heq, hcached] at houtput
  cases houtput
  exact hnext

theorem rootCache_preserved {α : Type} (parameter : PublicParameter) (leafIndex : LeafIndex)
    (root : Digest) (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hroot : RootCache parameter leafIndex root initialCache)
    (hbound : computation.IsQueryBoundP (AtHashAddress parameter (finalRootDomain leafIndex)) 0)
    (hmem : (result, finalCache) ∈ support ((simulateQ randomOracle computation).run initialCache)) :
    RootCache parameter leafIndex root finalCache := by
  intro input output haddress houtput
  cases hcached : initialCache input with
  | none =>
      have hnone := CacheReplay.cache_none_of_zero_query_bound computation input
        initialCache finalCache result (hbound.of_imp (fun candidate heq => heq ▸ haddress)) hcached hmem
      rw [houtput] at hnone
      contradiction
  | some cached =>
      have hpersist := CacheReplay.randomOracle_cache_le computation initialCache (result, finalCache) hmem hcached
      dsimp only at hpersist
      rw [houtput] at hpersist
      cases hpersist
      exact hroot _ _ haddress hcached

theorem rootCache_after_signing (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (root : Digest) (request : SignRequest) (answer : Option Generic.Signature)
    (initialCache finalCache : QueryCache HashSpec)
    (hroot : RootCache secretKey.parameter leafIndex root initialCache)
    (hsign : (answer, finalCache) ∈ support ((simulateQ romImpl
      (Signing.precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    RootCache secretKey.parameter leafIndex root finalCache := by
  intro input output haddress houtput
  rw [Signing.precomputedCappedSign] at hsign
  have heq := Signing.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit
    secretKey request.epoch request.message input (fun randomness heq => by
      rw [← heq] at haddress
      simp [CacheView.encodingInput, finalRootDomain] at haddress)
    initialCache finalCache answer hsign
  rw [heq] at houtput
  exact hroot input output haddress houtput

theorem rootCache_cache_encoding (parameter : PublicParameter) (leafIndex : LeafIndex)
    (root : Digest) (cache : QueryCache HashSpec) (hroot : RootCache parameter leafIndex root cache)
    (epoch : LeafIndex) (message : Message) (randomness : Randomness) (output : Digest) :
    RootCache parameter leafIndex root
      (cache.cacheQuery (CacheView.encodingInput parameter epoch (message, randomness)) output) := by
  intro input answer haddress hcached
  have hne : input ≠ CacheView.encodingInput parameter epoch (message, randomness) := by
    intro heq
    rw [heq] at haddress
    simp [CacheView.encodingInput, finalRootDomain] at haddress
  rw [QueryCache.cacheQuery_of_ne _ _ hne] at hcached
  exact hroot input answer haddress hcached

theorem authenticationRoot_avoids_finalRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (levels : ℕ) (hlevels : levels ≤ 31) (leaf : Digest) :
    (Generic.Verify.authenticationRoot parameter leafIndex signature levels leaf : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (finalRootDomain leafIndex)) 0 := by
  induction levels with
  | zero => simp [Generic.Verify.authenticationRoot]
  | succ levels ih =>
      rw [Generic.Verify.authenticationRoot]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih (by omega)) ?_
      intro current _
      unfold Generic.Verify.authenticationNodeHash
      split
      · split <;> apply Hashing.tweakableHash_queryBound_atOtherAddress
        all_goals simp only [finalRootDomain, finalRootLevel, ne_eq, Generic.HashDomain.merkle.injEq, Fin.mk.injEq]
        all_goals omega
      · simp

theorem recoverEndpoints_avoids_finalRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Generic.Signature) :
    (Generic.Verify.recoverEndpoints parameter leafIndex encoding signature : OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
      (AtHashAddress parameter (finalRootDomain leafIndex)) 0 := by
  unfold Generic.Verify.recoverEndpoints
  apply sequenceFin_queryBound_zero
  intro chain
  exact Wots.chainWalk_queryBound_zero_merkleAddress _ _ _ _ _ _ _ _

theorem finalRootHash_probability_ge (parameter : PublicParameter) (leafIndex : LeafIndex)
    (root current sibling : Digest) (cache : QueryCache HashSpec)
    (hroot : RootCache parameter leafIndex root cache) :
    ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ ≤
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = root |
        (simulateQ randomOracle (Generic.Verify.authenticationNodeHash parameter leafIndex 31 current sibling :
          OracleComp HashSpec Digest)).run cache] := by
  have hnode (left right : Digest) :
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ ≤
        Pr[fun result : Digest × QueryCache HashSpec => result.1 = root |
          (simulateQ randomOracle (Generic.Hashing.nodeHash parameter finalRootLevel
            (Generic.Merkle.nodeIndex leafIndex 31) left right : OracleComp HashSpec Digest)).run cache] := by
    let input := CacheView.merkleInput parameter finalRootLevel (Generic.Merkle.nodeIndex leafIndex 31) left right
    have haddress : AtHashAddress parameter (finalRootDomain leafIndex) input := by
      simp [input, CacheView.merkleInput, finalRootDomain, finalRootLevel]
    change _ ≤ Pr[fun result : Digest × QueryCache HashSpec => result.1 = root |
      (fun result : Digest × QueryCache HashSpec => (result.1, result.2)) <$>
        (randomOracle input).run cache]
    rw [probEvent_map]
    cases hcached : cache input with
    | none =>
        rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, probEvent_map]
        simpa only [Function.comp_def, uniformHashOutput] using
          (RandomOracle.uniform_eq_probability root).ge
    | some output =>
        rw [QueryImpl.withCaching_run_some _ hcached]
        simp only [Function.comp_def, probEvent_pure, hroot _ _ haddress hcached, if_true]
        norm_num [digestBits]
  unfold Generic.Verify.authenticationNodeHash
  rw [dif_pos (by decide : 31 < treeHeight)]
  split
  · exact hnode sibling current
  · exact hnode current sibling

theorem le_probEvent_bind_of_forall_le {α β : Type} (first : ProbComp α)
    (next : α → ProbComp β) (event : β → Prop) (bound : ℝ≥0∞)
    (hbound : ∀ value ∈ support first, bound ≤ Pr[event | next value]) :
    bound ≤ Pr[event | first >>= next] := by
  have hmass : ∑' value, Pr[= value | first] = 1 := tsum_probOutput_eq_one' (by simp)
  calc
    bound = ∑' value, Pr[= value | first] * bound := by rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      rw [probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hmem : value ∈ support first
      · exact mul_le_mul' le_rfl (hbound value hmem)
      · rw [probOutput_eq_zero_of_not_mem_support hmem]
        simp

theorem verifyAfterLeaf_probability_ge (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (leaf : Digest) (cache : QueryCache HashSpec)
    (hroot : RootCache publicKey.parameter leafIndex publicKey.root cache) :
    ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ ≤
      Pr[fun result : Bool × QueryCache HashSpec => result.1 = true |
        (simulateQ randomOracle (Generic.Verify.verifyAfterLeaf publicKey leafIndex signature leaf :
          OracleComp HashSpec Bool)).run cache] := by
  rw [Generic.Verify.verifyAfterLeaf]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map, probEvent_map,
    Function.comp_def, decide_eq_true_eq]
  rw [show treeHeight = 31 + 1 from rfl, Generic.Verify.authenticationRoot, simulateQ_bind, StateT.run_bind]
  refine le_probEvent_bind_of_forall_le
    ((simulateQ randomOracle (Generic.Verify.authenticationRoot publicKey.parameter leafIndex signature 31 leaf :
      OracleComp HashSpec Digest)).run cache)
    (fun result : Digest × QueryCache HashSpec => (simulateQ randomOracle
      (Generic.Verify.authenticationNodeHash publicKey.parameter leafIndex 31 result.1 (Generic.Verify.signaturePath signature 31) :
        OracleComp HashSpec Digest)).run result.2)
    (fun result => result.1 = publicKey.root) _ ?_
  rintro ⟨current, middleCache⟩ hmem
  have havoid := authenticationRoot_avoids_finalRoot publicKey.parameter leafIndex signature 31
    (Nat.le_refl 31) leaf
  have hmiddle : RootCache publicKey.parameter leafIndex publicKey.root middleCache := by
    exact rootCache_preserved publicKey.parameter leafIndex publicKey.root
        (Generic.Verify.authenticationRoot publicKey.parameter leafIndex signature 31 leaf : OracleComp HashSpec Digest)
        cache middleCache current hroot havoid hmem
  exact finalRootHash_probability_ge publicKey.parameter leafIndex publicKey.root current _ middleCache hmiddle

/-- Every accepted encoding has at least the final root-hash collision probability,
even if the remaining signature components are arbitrary. -/
theorem verify_cached_encoding_probability_ge (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Generic.Signature) (encoding : Encoding) (cache : QueryCache HashSpec)
    (hroot : RootCache publicKey.parameter leafIndex publicKey.root cache)
    (hdecode : Code.decodeDigest (CacheView.encodingHash cache publicKey.parameter
      leafIndex (message, signature.randomness)) = some encoding) :
    ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ ≤
      Pr[fun result : Bool × QueryCache HashSpec => result.1 = true |
        (simulateQ randomOracle (Generic.Verify.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run cache] := by
  rw [Generic.Verify.verify, simulateQ_bind, StateT.run_bind,
    Attack.encodingHash_run_cached _ _ _ _ _ _
      (TargetSum.decodedEncoding_of_decodeDigest hdecode), pure_bind, hdecode]
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall_le
  rintro ⟨endpoints, middleCache⟩ hmem
  have hmiddle := rootCache_preserved _ _ _ _ cache middleCache endpoints hroot
    (recoverEndpoints_avoids_finalRoot _ _ _ _) hmem
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall_le
  rintro ⟨leaf, leafCache⟩ hleaf
  exact verifyAfterLeaf_probability_ge _ _ _ _ _
    (rootCache_preserved _ _ _ _ middleCache leafCache leaf hmiddle
      (Hashing.tweakableHash_queryBound_atOtherAddress _ _ _ _ (by simp [finalRootDomain])) hleaf)

/-- info: 'Xmss.TargetSum.EUFCMA.verify_cached_encoding_probability_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verify_cached_encoding_probability_ge

end Xmss.TargetSum.EUFCMA

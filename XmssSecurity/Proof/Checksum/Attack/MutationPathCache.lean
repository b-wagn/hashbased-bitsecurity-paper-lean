import XmssSecurity.Proof.Checksum.Attack.MutationPath
import XmssSecurity.Proof.Checksum.Direct.DecidingCache

/-! The key-generation cache contains exactly the honest input at each mutation-path address. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

def mutationHonestValue (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) (position : ℕ) : Digest :=
  if position ≤ mutationChainSteps digit then
    Wots.walk (CacheView.chainStep cache secretKey.parameter leafIndex chain)
      0 (digit.val + position) (secretKey.chainStart leafIndex chain)
  else
    CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart
      (position - (mutationChainSteps digit + 1))
      (CacheReplay.pathNode leafIndex (position - (mutationChainSteps digit + 1)))

theorem mutationHonestValue_chain (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) (position : ℕ)
    (hposition : position ≤ mutationChainSteps digit) :
    mutationHonestValue cache secretKey leafIndex chain digit position =
      Wots.walk (CacheView.chainStep cache secretKey.parameter leafIndex chain)
        0 (digit.val + position) (secretKey.chainStart leafIndex chain) := by
  simp only [mutationHonestValue, if_pos hposition]

theorem mutationHonestValue_tree (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) (level : ℕ) :
    mutationHonestValue cache secretKey leafIndex chain digit (mutationChainSteps digit + 1 + level) =
      CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart level
        (CacheReplay.pathNode leafIndex level) := by
  have h : ¬mutationChainSteps digit + 1 + level ≤ mutationChainSteps digit := by omega
  simp [mutationHonestValue, h]

theorem mutationHonestValue_start (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness) :
    mutationHonestValue cache secretKey leafIndex chain (encoding chain) 0 =
      (CacheReplay.signWithEncoding cache secretKey leafIndex randomness encoding).chainValue chain := by
  simp [mutationHonestValue, CacheReplay.signWithEncoding, CacheReplay.signedChainValues]

theorem mutationHonestValue_endpoint (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    mutationHonestValue cache secretKey leafIndex chain digit (mutationChainSteps digit) =
      CacheReplay.oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex chain := by
  rw [mutationHonestValue_chain _ _ _ _ _ _ le_rfl]
  have hdigit : digit.val + mutationChainSteps digit = chainLength - 1 := by
    have h := digit.isLt
    unfold mutationChainSteps
    omega
  rw [hdigit]
  rfl

theorem mutationPathInput_cached_unique
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (position : ℕ)
    (hposition : position < mutationChainSteps digit + 1 + treeHeight)
    (left right : Digest) (leftOutput rightOutput : HashOutput)
    (hleft : keyResult.2
      (mutationPathInput keyResult.1.2.parameter leafIndex chain digit signature endpoints position left) =
        some leftOutput)
    (hright : keyResult.2
      (mutationPathInput keyResult.1.2.parameter leafIndex chain digit signature endpoints position right) =
        some rightOutput) : left = right := by
  apply mutationPathInput_injective keyResult.1.2.parameter leafIndex chain digit
    signature endpoints position hposition
  have hold := precomputedKeygen_support_oldKeygen keyResult hkey
  by_cases hchain : position < mutationChainSteps digit
  · rw [mutationPathInput_chain _ _ _ _ _ _ _ hchain] at hleft hright ⊢
    rw [mutationPathInput_chain _ _ _ _ _ _ _ hchain]
    exact keygen_cache_unique_chainAddress _ hold leafIndex chain
      ⟨digit.val + position, by unfold mutationChainSteps at hchain; omega⟩
      _ _ leftOutput rightOutput
      (by simp [CacheView.chainInput, erasePrecomputation, SecretKey.withoutPrecomputation])
      (by simp [CacheView.chainInput, erasePrecomputation, SecretKey.withoutPrecomputation]) hleft hright
  · by_cases hleaf : position = mutationChainSteps digit
    · subst position
      rw [mutationPathInput_leaf] at hleft hright ⊢
      rw [mutationPathInput_leaf]
      exact keygen_cache_unique_leafAddress _ hold leafIndex _ _ leftOutput rightOutput
        (by simp [CacheView.leafInput, erasePrecomputation, SecretKey.withoutPrecomputation])
        (by simp [CacheView.leafInput, erasePrecomputation, SecretKey.withoutPrecomputation]) hleft hright
    · let level := position - (mutationChainSteps digit + 1)
      have hlevel : level < treeHeight := by dsimp [level]; omega
      have hpos : position = mutationChainSteps digit + 1 + level := by dsimp [level]; omega
      rw [hpos, mutationPathInput_node _ _ _ _ _ _ _ hlevel] at hleft hright ⊢
      rw [mutationPathInput_node _ _ _ _ _ _ _ hlevel]
      exact keygen_cache_unique_merkleAddress _ hold ⟨level, hlevel⟩
        (CacheView.nodeIndex leafIndex level) _ _ leftOutput rightOutput
        (by simp [CacheView.nodeInput, erasePrecomputation, SecretKey.withoutPrecomputation])
        (by simp [CacheView.nodeInput, erasePrecomputation, SecretKey.withoutPrecomputation]) hleft hright

/-- The mutation path with its unchanged components taken from the honest signature. -/
def mutationReplayInputs (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness) :
    ℕ → Digest → HashInput :=
  mutationPathInput secretKey.parameter leafIndex chain (encoding chain)
    (CacheReplay.signWithEncoding cache secretKey leafIndex randomness encoding)
    (CacheReplay.oneTimePublicKey cache secretKey.parameter secretKey.chainStart leafIndex)

theorem mutationReplayInputs_digestAt (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (position : ℕ) (hposition : position < mutationChainSteps (encoding chain) + 1 + treeHeight) :
    CacheView.digestAt cache (mutationReplayInputs cache secretKey leafIndex chain encoding randomness
      position (mutationHonestValue cache secretKey leafIndex chain (encoding chain) position)) =
      mutationHonestValue cache secretKey leafIndex chain (encoding chain) (position + 1) := by
  unfold mutationReplayInputs
  by_cases hchain : position < mutationChainSteps (encoding chain)
  · rw [mutationPathInput_chain _ _ _ _ _ _ _ hchain,
      mutationHonestValue_chain _ _ _ _ _ _ (by omega),
      mutationHonestValue_chain _ _ _ _ _ _ (by omega)]
    have hstep : (encoding chain).val + position < chainLength - 1 := by
      unfold mutationChainSteps at hchain
      omega
    rw [show (encoding chain).val + (position + 1) = (encoding chain).val + position + 1 by omega,
      Wots.walk, CacheView.chainStep, Nat.zero_add, dif_pos hstep]
  · by_cases hleaf : position = mutationChainSteps (encoding chain)
    · subst position
      rw [mutationPathInput_leaf, mutationHonestValue_endpoint, Function.update_eq_self]
      have hnext := mutationHonestValue_tree cache secretKey leafIndex chain (encoding chain) 0
      rw [Nat.add_zero] at hnext
      rw [hnext, CacheReplay.pathNode_zero, CacheReplay.treeNode_zero_eq]
      rfl
    · let level := position - (mutationChainSteps (encoding chain) + 1)
      have hlevel : level < treeHeight := by dsimp [level]; omega
      have hpos : position = mutationChainSteps (encoding chain) + 1 + level := by dsimp [level]; omega
      rw [hpos, mutationPathInput_node _ _ _ _ _ _ _ hlevel, mutationHonestValue_tree,
        show mutationChainSteps (encoding chain) + 1 + level + 1 =
          mutationChainSteps (encoding chain) + 1 + (level + 1) by omega,
        mutationHonestValue_tree]
      have hsibling : signaturePath (CacheReplay.signWithEncoding cache secretKey leafIndex randomness encoding)
          level = CacheReplay.treeNode cache secretKey.parameter secretKey.chainStart level
            (authenticationPathNode leafIndex ⟨level, hlevel⟩) := by
        simp [signaturePath, CacheReplay.signWithEncoding, CacheReplay.authenticationPath, hlevel]
      rw [hsibling]
      have hstep := CacheReplay.authentication_step_eq_treeNode cache secretKey.parameter
        secretKey.chainStart leafIndex level hlevel
      simpa only [CacheView.nodeHash, dif_pos hlevel] using hstep

theorem mutationReplayInputs_cached
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (position : ℕ) (hposition : position < mutationChainSteps (encoding chain) + 1 + treeHeight) :
    ∃ output, keyResult.2 (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness
        position (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain) position)) =
      some output := by
  unfold mutationReplayInputs
  by_cases hchain : position < mutationChainSteps (encoding chain)
  · rw [mutationPathInput_chain _ _ _ _ _ _ _ hchain,
      mutationHonestValue_chain _ _ _ _ _ _ (by omega)]
    exact precomputedKeygen_cache_has_chainInput keyResult hkey leafIndex chain _
  · by_cases hleaf : position = mutationChainSteps (encoding chain)
    · subst position
      rw [mutationPathInput_leaf, mutationHonestValue_endpoint, Function.update_eq_self]
      exact keygen_cache_has_leafInput _ (precomputedKeygen_support_oldKeygen keyResult hkey) leafIndex
    · let level := position - (mutationChainSteps (encoding chain) + 1)
      have hlevel : level < treeHeight := by dsimp [level]; omega
      have hpos : position = mutationChainSteps (encoding chain) + 1 + level := by dsimp [level]; omega
      rw [hpos, mutationPathInput_node _ _ _ _ _ _ _ hlevel, mutationHonestValue_tree]
      have hsibling : signaturePath (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
          leafIndex randomness encoding) level = CacheReplay.treeNode keyResult.2
            keyResult.1.2.parameter keyResult.1.2.chainStart level
            (authenticationPathNode leafIndex ⟨level, hlevel⟩) := by
        simp [signaturePath, CacheReplay.signWithEncoding, CacheReplay.authenticationPath, hlevel]
      rw [hsibling, CappedMerkle.nodeInput_eq_merkleInput_ordered,
        CappedMerkle.ordered_honestNodePair_eq_children]
      exact precomputedKeygen_cache_has_merkleInput_in_largerCache keyResult hkey keyResult.2
        le_rfl ⟨level, hlevel⟩ _ (CappedMerkle.nodeIndex_valid_at_level leafIndex ⟨level, hlevel⟩)

theorem mutationReplayInputs_honest
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (position : ℕ) (hposition : position < mutationChainSteps (encoding chain) + 1 + treeHeight) :
    ∃ output, keyResult.2 (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness
        position (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain) position)) =
      some output ∧ truncateHash output =
        mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain) (position + 1) := by
  obtain ⟨output, houtput⟩ := mutationReplayInputs_cached keyResult hkey leafIndex chain encoding
    randomness position hposition
  refine ⟨output, houtput, ?_⟩
  rw [← CacheView.digestAt_eq_of_cache_eq_some houtput]
  exact mutationReplayInputs_digestAt _ _ _ _ _ _ _ hposition

theorem mutationReplayInputs_fresh
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (position : ℕ) (hposition : position < mutationChainSteps (encoding chain) + 1 + treeHeight)
    (other : Digest)
    (hne : other ≠ mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain) position) :
    keyResult.2 (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness
      position other) = none := by
  obtain ⟨honestOutput, hhonest⟩ := mutationReplayInputs_cached keyResult hkey leafIndex chain
    encoding randomness position hposition
  cases hother : keyResult.2 (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding
      randomness position other) with
  | none => rfl
  | some output =>
      exact False.elim (hne (mutationPathInput_cached_unique keyResult hkey leafIndex chain
        (encoding chain) _ _ position hposition _ _ output honestOutput hother hhonest))

theorem mutationHonestValue_root
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain digit
      (mutationChainSteps digit + 1 + treeHeight) = keyResult.1.1.root := by
  rw [mutationHonestValue_tree]
  have hnode : CacheReplay.pathNode leafIndex treeHeight = rootNode := by
    apply Fin.ext
    have hdiv : leafIndex.val / 2 ^ treeHeight = 0 := Nat.div_eq_of_lt leafIndex.isLt
    simp [CacheReplay.pathNode, rootNode, merkleNodeOfNat, hdiv]
  rw [hnode]
  have hold := precomputedKeygen_support_oldKeygen keyResult hkey
  obtain ⟨parameter, secret, root, hpair, hroot⟩ := keygen_support_rootTree _ hold
  have hparameter : keyResult.1.2.parameter = parameter :=
    congrArg (fun pair : PublicKey × SecretKey => pair.2.parameter) hpair
  have hsecret : keyResult.1.2.chainStart = secret :=
    congrArg (fun pair : PublicKey × SecretKey => pair.2.chainStart) hpair
  have hrootEq : keyResult.1.1.root = root :=
    congrArg (fun pair : PublicKey × SecretKey => pair.1.root) hpair
  rw [hparameter, hsecret, hrootEq]
  rw [← CacheReplay.eval_treeNode]
  exact CacheReplay.eval_answerFn_finalCache_eq_of_mem_support _ _ _ _ hroot

/-- info: 'XmssSecurity.Checksum.Attack.mutationReplayInputs_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationReplayInputs_fresh

/-- info: 'XmssSecurity.Checksum.Attack.mutationHonestValue_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationHonestValue_root

end XmssSecurity.Checksum.Attack

import XmssSecurity.Proof.Checksum.FreshPathProbability
import XmssSecurity.Proof.Checksum.Attack.ChainMutation

/-! The altered chain, leaf, and authentication nodes form one hash path. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum

theorem Rom.hashPath_append (inputs : ℕ → Digest → HashInput) (start first rest : ℕ)
    (value : Digest) :
    hashPath inputs start (first + rest) value =
      hashPath inputs start first value >>= hashPath inputs (start + first) rest := by
  induction first generalizing start value with
  | zero => simp [hashPath]
  | succ first ih =>
      rw [Nat.succ_add, hashPath, hashPath, bind_assoc]
      apply bind_congr
      intro output
      rw [ih]
      rw [show start + 1 + first = start + (first + 1) by omega]

theorem Rom.hashPath_snoc (inputs : ℕ → Digest → HashInput) (start steps : ℕ)
    (value : Digest) :
    hashPath inputs start (steps + 1) value = do
      let previous ← hashPath inputs start steps value
      let output ← liftM (HashSpec.query (inputs (start + steps) previous))
      return truncateHash output := by
  rw [hashPath_append]
  rfl

namespace Attack

open Concrete

def mutationChainSteps (digit : Digit) : ℕ := chainLength - 1 - digit.val

def mutationPathInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (position : ℕ) (value : Digest) : HashInput :=
  if hchain : position < mutationChainSteps digit then
    CacheView.chainInput parameter leafIndex chain
      ⟨digit.val + position, by unfold mutationChainSteps at hchain; omega⟩ value
  else if position = mutationChainSteps digit then
    CacheView.leafInput parameter leafIndex (Function.update endpoints chain value)
  else if hlevel : position - (mutationChainSteps digit + 1) < treeHeight then
    CacheView.nodeInput parameter leafIndex
      ⟨position - (mutationChainSteps digit + 1), hlevel⟩ value
      (signaturePath signature (position - (mutationChainSteps digit + 1)))
  else []

theorem mutationPathInput_chain (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (position : ℕ) (hposition : position < mutationChainSteps digit)
    (value : Digest) :
    mutationPathInput parameter leafIndex chain digit signature endpoints position value =
      CacheView.chainInput parameter leafIndex chain
        ⟨digit.val + position, by unfold mutationChainSteps at hposition; omega⟩ value := by
  simp only [mutationPathInput, dif_pos hposition]

theorem mutationPathInput_leaf (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (value : Digest) :
    mutationPathInput parameter leafIndex chain digit signature endpoints (mutationChainSteps digit) value =
      CacheView.leafInput parameter leafIndex (Function.update endpoints chain value) := by
  simp [mutationPathInput]

theorem mutationPathInput_node (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (level : ℕ) (hlevel : level < treeHeight) (value : Digest) :
    mutationPathInput parameter leafIndex chain digit signature endpoints
      (mutationChainSteps digit + 1 + level) value =
      CacheView.nodeInput parameter leafIndex ⟨level, hlevel⟩ value (signaturePath signature level) := by
  have hchain : ¬mutationChainSteps digit + 1 + level < mutationChainSteps digit := by omega
  have hleaf : mutationChainSteps digit + 1 + level ≠ mutationChainSteps digit := by omega
  simp [mutationPathInput, hchain, hleaf, hlevel]

theorem mutationPath_length (digit : Digit) :
    mutationChainSteps digit + 1 + treeHeight = 40 - digit.val := by
  have hdigit := digit.isLt
  norm_num [chainLength, winternitzBits] at hdigit
  norm_num [mutationChainSteps, chainLength, winternitzBits, treeHeight]
  omega

theorem mutationPath_chain (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (steps : ℕ) (hsteps : steps ≤ mutationChainSteps digit)
    (value : Digest) :
    Rom.hashPath (mutationPathInput parameter leafIndex chain digit signature endpoints) 0 steps value =
      (chainWalk parameter leafIndex chain digit.val steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hchain : steps < mutationChainSteps digit := by omega
      have hposition : digit.val + steps < chainLength - 1 := by
        unfold mutationChainSteps at hchain
        omega
      rw [Rom.hashPath_snoc, ih (by omega), chainWalk]
      apply bind_congr
      intro previous
      rw [show 0 + steps = steps from Nat.zero_add _, mutationPathInput_chain _ _ _ _ _ _ _ hchain,
        dif_pos hposition]
      simp only [chainHash, tweakableHash, oracleHash, HasQuery.instOfMonadLift_query,
        CacheView.chainInput, digestBytes]

theorem mutationPath_leaf (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (value : Digest) :
    Rom.hashPath (mutationPathInput parameter leafIndex chain digit signature endpoints)
      (mutationChainSteps digit) 1 value =
        (leafHash parameter leafIndex (Function.update endpoints chain value) :
          OracleComp HashSpec Digest) := by
  rw [Rom.hashPath, mutationPathInput_leaf]
  simp [Rom.hashPath, leafHash, tweakableHash, oracleHash,
    HasQuery.instOfMonadLift_query, CacheView.leafInput]

theorem mutationPath_authentication (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (levels : ℕ) (hlevels : levels ≤ treeHeight)
    (leaf : Digest) :
    Rom.hashPath (mutationPathInput parameter leafIndex chain digit signature endpoints)
      (mutationChainSteps digit + 1) levels leaf =
        (authenticationRoot parameter leafIndex signature levels leaf : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have hlevel : levels < treeHeight := by omega
      rw [Rom.hashPath_snoc, ih (by omega), authenticationRoot]
      apply bind_congr
      intro current
      rw [mutationPathInput_node _ _ _ _ _ _ _ hlevel]
      unfold authenticationNodeHash
      rw [dif_pos hlevel]
      cases hbit : leafIndex.val.testBit levels with
      | false =>
          have hinput : CacheView.nodeInput parameter leafIndex ⟨levels, hlevel⟩ current
              (signaturePath signature levels) = CacheView.merkleInput parameter ⟨levels, hlevel⟩
                (nodeIndex leafIndex levels) current (signaturePath signature levels) := by
            simp [CacheView.nodeInput, CacheView.authenticationNodePayload, CacheView.merkleInput, hbit]
          rw [hinput]
          simp [nodeHash, tweakableHash, oracleHash, HasQuery.instOfMonadLift_query,
            CacheView.merkleInput]
      | true =>
          have hinput : CacheView.nodeInput parameter leafIndex ⟨levels, hlevel⟩ current
              (signaturePath signature levels) = CacheView.merkleInput parameter ⟨levels, hlevel⟩
                (nodeIndex leafIndex levels) (signaturePath signature levels) current := by
            simp [CacheView.nodeInput, CacheView.authenticationNodePayload, CacheView.merkleInput, hbit]
          rw [hinput]
          simp [nodeHash, tweakableHash, oracleHash, HasQuery.instOfMonadLift_query,
            CacheView.merkleInput]

/-- The selected chain is recovered, inserted into the honest endpoints, and followed to the
root. The other chains are accounted for separately as cache hits. -/
def mutationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (value : Digest) : OracleComp HashSpec Digest := do
  let endpoint ← recoverChain parameter leafIndex chain digit value
  let leaf ← leafHash parameter leafIndex (Function.update endpoints chain endpoint)
  authenticationRoot parameter leafIndex signature treeHeight leaf

theorem mutationRoot_eq_hashPath (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (value : Digest) :
    mutationRoot parameter leafIndex chain digit signature endpoints value =
      Rom.hashPath (mutationPathInput parameter leafIndex chain digit signature endpoints)
        0 (40 - digit.val) value := by
  unfold mutationRoot recoverChain
  rw [← mutationPath_length, Rom.hashPath_append, Rom.hashPath_append, bind_assoc]
  simp only [Nat.zero_add]
  rw [mutationPath_chain _ _ _ _ _ _ _ le_rfl]
  apply bind_congr
  intro endpoint
  rw [mutationPath_leaf]
  apply bind_congr
  intro leaf
  exact (mutationPath_authentication _ _ _ _ _ _ _ le_rfl leaf).symm

theorem mutationPathInput_separate (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (leftIndex rightIndex : ℕ)
    (hleft : leftIndex < mutationChainSteps digit + 1 + treeHeight)
    (hright : rightIndex < mutationChainSteps digit + 1 + treeHeight)
    (hne : leftIndex ≠ rightIndex) (left right : Digest) :
    mutationPathInput parameter leafIndex chain digit signature endpoints leftIndex left ≠
      mutationPathInput parameter leafIndex chain digit signature endpoints rightIndex right := by
  intro heq
  unfold mutationPathInput at heq
  split_ifs at heq
  all_goals try omega
  all_goals
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    simp only [HashDomain.chain.injEq, HashDomain.merkle.injEq,
      reduceCtorEq, Fin.mk.injEq, true_and] at hdomain
  all_goals omega

private theorem nodeInput_current_injective (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : MerkleLevel) (sibling : Digest) :
    Function.Injective (fun value => CacheView.nodeInput parameter leafIndex level value sibling) := by
  intro left right heq
  have hpayload := payload_eq_of_tweakableHashInput_eq parameter
    (.merkle level (nodeIndex leafIndex level.val)) heq
  change CacheView.authenticationNodePayload leafIndex level.val left sibling =
    CacheView.authenticationNodePayload leafIndex level.val right sibling at hpayload
  unfold CacheView.authenticationNodePayload at hpayload
  cases hbit : leafIndex.val.testBit level.val with
  | false =>
      simp only [hbit, Bool.false_eq_true, if_false] at hpayload
      exact congrArg Prod.fst (@nodePayload_injective (left, sibling) (right, sibling) hpayload)
  | true =>
      simp only [hbit, if_true] at hpayload
      exact congrArg Prod.snd (@nodePayload_injective (sibling, left) (sibling, right) hpayload)

theorem mutationPathInput_injective (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (position : ℕ)
    (hposition : position < mutationChainSteps digit + 1 + treeHeight) :
    Function.Injective (mutationPathInput parameter leafIndex chain digit signature endpoints position) := by
  intro left right heq
  unfold mutationPathInput at heq
  split_ifs at heq with hchain hleaf hlevel
  · exact CacheView.chainInput_injective _ _ _ _ heq
  · have h := CacheView.leafInput_injective _ _ heq
    simpa using congrArg (fun endpoints => endpoints chain) h
  · exact nodeInput_current_injective _ _ _ _ heq
  · omega

/-- info: 'XmssSecurity.Checksum.Attack.mutationRoot_eq_hashPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationRoot_eq_hashPath

end Attack

end XmssSecurity.Checksum

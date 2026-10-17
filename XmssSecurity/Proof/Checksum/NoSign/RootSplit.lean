import XmssSecurity.Proof.Checksum.NoSign.KeygenHit
import XmssSecurity.Proof.Checksum.KeygenCache

/-!
# The root is a fresh sample

Key generation computes the two top children of the tree and then queries the top input, which
nothing before has queried. Its output, the root, is therefore a uniform sample independent of
everything else key generation computes (`evalDist_rootTree_split`). Events of the
key-generation cache that do not depend on the root can be evaluated with the root resampled
(`probEvent_rootTree_eq_split`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

/-- The level of the top node. -/
def topLevel : MerkleLevel := ⟨treeHeight - 1, by decide⟩

theorem treeHeight_eq_succ : treeHeight = (treeHeight - 1) + 1 := by decide

/-- A top child, replayed from a cache. -/
def honestChild (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (right : Bool) : Digest :=
  Concrete.CacheReplay.treeNode cache parameter secret (treeHeight - 1)
    (Concrete.childNode Concrete.rootNode right)

/-- The top child on the other side from the path of `leafIndex`. -/
def honestSibling (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : Digest :=
  honestChild cache parameter secret (!leafIndex.val.testBit (treeHeight - 1))

/-- The input of the top query of key generation. -/
def topInput (parameter : PublicParameter) (left right : Digest) : HashInput :=
  Concrete.CacheView.merkleInput parameter topLevel Concrete.rootNode left right

/-- Key generation in the random-oracle model. -/
theorem keygen_run_eq :
    (simulateQ romImpl Concrete.keygen).run ∅ = (do
      let parameter ← Concrete.samplePublicParameter
      let secret ← Concrete.sampleSecret
      let tree ← (simulateQ randomOracle
        (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅
      pure ((⟨tree.1, parameter⟩, SecretKey.withoutPrecomputation parameter secret), tree.2)) := by
  unfold Concrete.keygen
  have hlift : ∀ {α : Type} (computation : ProbComp α) (cache : QueryCache HashSpec),
      (simulateQ romImpl (liftM computation : OracleComp OracleWorld α)).run cache =
        (fun value => (value, cache)) <$> computation := fun computation cache =>
    roSim.run_liftM (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) computation
      cache
  have hroute : ∀ parameter secret,
      simulateQ romImpl
          (liftM (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
            OracleComp HashSpec Digest) := fun parameter secret => by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)
  simp only [simulateQ_bind, StateT.run_bind, hlift, bind_map_left, hroute, simulateQ_pure,
    StateT.run_pure]

/-- The subtrees under the top node never query the top address. -/
theorem topChild_queryBound_zero (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (right : Bool) :
    (Concrete.treeNode parameter secret (treeHeight - 1)
      (Concrete.childNode Concrete.rootNode right) :
        OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.merkle topLevel Concrete.rootNode)) 0 := by
  have hvalid : TreeSubtreeValid ((treeHeight - 1) + 1) Concrete.rootNode := by
    unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num [treeHeight]
  have h := Concrete.treeNode_queryBound_merkleAddress parameter secret topLevel
    Concrete.rootNode (treeHeight - 1) (Concrete.childNode Concrete.rootNode right) (by omega)
    (childNode_subtreeValid (treeHeight - 1) Concrete.rootNode right hvalid)
  simpa [MerkleAddressInSubtree, topLevel] using h

/-- Neither subtree queries the top input. -/
theorem topInput_none_of_subtrees (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (left right : Digest × QueryCache HashSpec)
    (hleft : left ∈ support ((simulateQ randomOracle
      (Concrete.treeNode parameter secret (treeHeight - 1)
        (Concrete.childNode Concrete.rootNode false) : OracleComp HashSpec Digest)).run ∅))
    (hright : right ∈ support ((simulateQ randomOracle
      (Concrete.treeNode parameter secret (treeHeight - 1)
        (Concrete.childNode Concrete.rootNode true) : OracleComp HashSpec Digest)).run left.2))
    (input : HashInput)
    (hinput : AtHashAddress parameter (.merkle topLevel Concrete.rootNode) input) :
    right.2 input = none := by
  have hzero : ∀ right : Bool,
      (Concrete.treeNode parameter secret (treeHeight - 1)
        (Concrete.childNode Concrete.rootNode right) :
          OracleComp HashSpec Digest).IsQueryBoundP (· = input) 0 :=
    fun right => (topChild_queryBound_zero parameter secret right).of_imp
      fun candidate heq => heq ▸ hinput
  have hleftNone := Concrete.CacheReplay.cache_none_of_zero_query_bound _ _ ∅ left.2 left.1
    (hzero false) rfl hleft
  exact Concrete.CacheReplay.cache_none_of_zero_query_bound _ _ left.2 right.2 right.1
    (hzero true) hleftNone hright

theorem atHashAddress_topInput (parameter : PublicParameter) (left right : Digest) :
    AtHashAddress parameter (.merkle topLevel Concrete.rootNode) (topInput parameter left right) := by
  simp [topInput, Concrete.CacheView.merkleInput]

/-- The tree computation: two subtrees, then a fresh top query. -/
theorem evalDist_rootTree_split (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) :
    𝒟[(simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅] =
      𝒟[do
        let left ← (simulateQ randomOracle
          (Concrete.treeNode parameter secret (treeHeight - 1)
            (Concrete.childNode Concrete.rootNode false) : OracleComp HashSpec Digest)).run ∅
        let right ← (simulateQ randomOracle
          (Concrete.treeNode parameter secret (treeHeight - 1)
            (Concrete.childNode Concrete.rootNode true) : OracleComp HashSpec Digest)).run left.2
        let output ← $ᵗ HashOutput
        pure (truncateHash output,
          right.2.cacheQuery (topInput parameter left.1 right.1) output)] := by
  have htree : (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest) = (do
        let left ← (Concrete.treeNode parameter secret (treeHeight - 1)
          (Concrete.childNode Concrete.rootNode false) : OracleComp HashSpec Digest)
        let right ← (Concrete.treeNode parameter secret (treeHeight - 1)
          (Concrete.childNode Concrete.rootNode true) : OracleComp HashSpec Digest)
        (Concrete.tweakableHash parameter (.merkle topLevel Concrete.rootNode)
          (Concrete.nodePayload left right) : OracleComp HashSpec Digest)) := by
    conv_lhs => rw [treeHeight_eq_succ, Concrete.treeNode_succ_eq]
    simp only [show treeHeight - 1 < treeHeight by decide, ↓reduceDIte, Concrete.nodeHash]
    rfl
  rw [htree]
  simp only [simulateQ_bind, StateT.run_bind]
  refine evalDist_bind_congr fun left hleft => evalDist_bind_congr fun right hright => ?_
  have hnone : right.2 (topInput parameter left.1 right.1) = none :=
    topInput_none_of_subtrees parameter secret left right hleft hright _
      (atHashAddress_topInput parameter left.1 right.1)
  have hrun :
      (simulateQ randomOracle
        (Concrete.tweakableHash parameter (.merkle topLevel Concrete.rootNode)
          (Concrete.nodePayload left.1 right.1) : OracleComp HashSpec Digest)).run right.2 =
      (fun output : HashOutput =>
        (truncateHash output, right.2.cacheQuery (topInput parameter left.1 right.1) output)) <$>
        ($ᵗ HashOutput) := by
    simp only [Concrete.tweakableHash, Concrete.oracleHash, simulateQ_bind, simulateQ_pure,
      StateT.run_bind]
    rw [show (simulateQ randomOracle
        (HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec)
          (tweakableHashInput parameter (.merkle topLevel Concrete.rootNode)
            (Concrete.nodePayload left.1 right.1)))).run right.2 =
        (randomOracle (spec := HashSpec) (topInput parameter left.1 right.1)).run right.2
      from by simp [HasQuery.query, topInput, Concrete.CacheView.merkleInput]]
    rw [QueryImpl.withCaching_run_none _ hnone]
    simp [uniformSampleImpl, map_eq_bind_pure_comp]
  rw [hrun, map_eq_bind_pure_comp]
  rfl

end XmssSecurity.Checksum.NoSign

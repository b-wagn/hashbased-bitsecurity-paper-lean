import Xmss.Proof.Generic.KeygenCache
import Xmss.Proof.Generic.CausalTreeCoupling
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

def hashCacheLookup (cache : QueryCache HashSpec) (input : HashInput) :
    Option Digest :=
  cache input

def MerkleHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ level node, AtHashAddress parameter (.merkle level node) input

def LeafCacheOutputsCorrespond
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    hashCacheLookup left (CacheView.leafInput parameter leafIndex
      (leftEndpoints leafIndex)) =
    hashCacheLookup right (CacheView.leafInput parameter leafIndex
      (rightEndpoints leafIndex))

def LeafReplayOutputsCorrespond
    (parameter : PublicParameter)
    (leftSecret rightSecret : LeafIndex → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    hashCacheLookup leftCache (CacheView.leafInput parameter leafIndex
      (CacheReplay.oneTimePublicKey leftCache parameter
        leftSecret leafIndex)) =
    hashCacheLookup rightCache (CacheView.leafInput parameter leafIndex
      (CacheReplay.oneTimePublicKey rightCache parameter
        rightSecret leafIndex))

def ReplayEndpointsMatch
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ leafIndex,
    endpoints leafIndex =
      CacheReplay.oneTimePublicKey cache parameter secret leafIndex

theorem CacheView.chainInput_ne_merkleInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    CacheView.chainInput parameter leafIndex chain step value ≠
      CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem CacheView.chainInput_ne_leafInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (targetLeafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    CacheView.chainInput parameter leafIndex chain step value ≠
      CacheView.leafInput parameter targetLeafIndex endpoints := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem CacheView.leafInput_ne_merkleInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) :
    CacheView.leafInput parameter leafIndex endpoints ≠
      CacheView.merkleInput parameter level node left right := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  simp at hdomain

theorem CacheView.chainStep_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : Digest)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    CacheView.chainStep
        (cache.cacheQuery
          (CacheView.merkleInput parameter level node left right)
          output) parameter leafIndex chain =
      CacheView.chainStep cache parameter leafIndex chain := by
  funext position value
  unfold CacheView.chainStep
  split
  · unfold CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact CacheView.chainInput_ne_merkleInput parameter leafIndex chain
      _ value level node left right
  · rfl

theorem CacheView.chainStep_cacheQuery_leafInput
    (cache : QueryCache HashSpec) (output : Digest)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (targetLeafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CacheView.chainStep
        (cache.cacheQuery
          (CacheView.leafInput parameter targetLeafIndex endpoints)
          output) parameter leafIndex chain =
      CacheView.chainStep cache parameter leafIndex chain := by
  funext position value
  unfold CacheView.chainStep
  split
  · unfold CacheView.digestAt
    rw [QueryCache.cacheQuery_of_ne]
    exact CacheView.chainInput_ne_leafInput parameter leafIndex chain
      _ value targetLeafIndex endpoints
  · rfl

theorem CacheReplay.oneTimePublicKey_cacheQuery_merkleInput
    (cache : QueryCache HashSpec) (output : Digest)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (CacheView.merkleInput parameter level node left right)
          output) parameter secret leafIndex =
      CacheReplay.oneTimePublicKey cache parameter secret leafIndex := by
  unfold CacheReplay.oneTimePublicKey
  funext chain
  rw [CacheView.chainStep_cacheQuery_merkleInput]

theorem CacheReplay.oneTimePublicKey_cacheQuery_leafInput
    (cache : QueryCache HashSpec) (output : Digest)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex targetLeafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CacheReplay.oneTimePublicKey
        (cache.cacheQuery
          (CacheView.leafInput parameter targetLeafIndex endpoints)
          output) parameter secret leafIndex =
      CacheReplay.oneTimePublicKey cache parameter secret leafIndex := by
  unfold CacheReplay.oneTimePublicKey
  funext chain
  rw [CacheView.chainStep_cacheQuery_leafInput]

theorem ReplayEndpointsMatch.cacheQuery_merkleInput
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest)
    (output : Digest) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (CacheView.merkleInput parameter level node left right)
        output) := by
  intro leafIndex
  rw [CacheReplay.oneTimePublicKey_cacheQuery_merkleInput]
  exact hrel leafIndex

theorem ReplayEndpointsMatch.cacheQuery_leafInput
    (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest)
    (endpoints : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hrel : ReplayEndpointsMatch parameter secret endpoints cache)
    (targetLeafIndex : LeafIndex) (targetEndpoints : ChainIndex → Digest)
    (output : Digest) :
    ReplayEndpointsMatch parameter secret endpoints
      (cache.cacheQuery
        (CacheView.leafInput parameter targetLeafIndex targetEndpoints)
        output) := by
  intro leafIndex
  rw [CacheReplay.oneTimePublicKey_cacheQuery_leafInput]
  exact hrel leafIndex

theorem LeafCacheOutputsCorrespond.cacheQuery_distinct
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leftInput rightInput : HashInput) (output : Digest)
    (hleft : ∀ leafIndex, leftInput ≠ CacheView.leafInput parameter
      leafIndex (leftEndpoints leafIndex))
    (hright : ∀ leafIndex, rightInput ≠ CacheView.leafInput parameter
      leafIndex (rightEndpoints leafIndex)) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery leftInput output) (right.cacheQuery rightInput output) := by
  intro leafIndex
  unfold hashCacheLookup
  rw [QueryCache.cacheQuery_of_ne left output (hleft leafIndex).symm,
    QueryCache.cacheQuery_of_ne right output (hright leafIndex).symm]
  exact hrel leafIndex

theorem CacheView.leafInput_eq_iff
    (parameter : PublicParameter)
    (leftLeafIndex rightLeafIndex : LeafIndex)
    (leftEndpoints rightEndpoints : ChainIndex → Digest) :
    CacheView.leafInput parameter leftLeafIndex leftEndpoints =
        CacheView.leafInput parameter rightLeafIndex rightEndpoints ↔
      leftLeafIndex = rightLeafIndex ∧ leftEndpoints = rightEndpoints := by
  constructor
  · intro heq
    have hleafIndex : leftLeafIndex = rightLeafIndex := by
      have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
      simpa using hdomain
    subst rightLeafIndex
    exact ⟨rfl, CacheView.leafInput_injective parameter leftLeafIndex heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem LeafCacheOutputsCorrespond.cacheQuery_pair
    (parameter : PublicParameter)
    (leftEndpoints rightEndpoints : LeafIndex → ChainIndex → Digest)
    (left right : QueryCache HashSpec)
    (hrel : LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      left right)
    (leafIndex : LeafIndex) (output : Digest) :
    LeafCacheOutputsCorrespond parameter leftEndpoints rightEndpoints
      (left.cacheQuery
        (CacheView.leafInput parameter leafIndex (leftEndpoints leafIndex))
          output)
      (right.cacheQuery
        (CacheView.leafInput parameter leafIndex (rightEndpoints leafIndex))
          output) := by
  intro candidate
  unfold hashCacheLookup
  by_cases hleafIndex : candidate = leafIndex
  · subst candidate
    simp only [QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne left output (by
        intro heq
        exact hleafIndex ((CacheView.leafInput_eq_iff parameter candidate
          leafIndex (leftEndpoints candidate) (leftEndpoints leafIndex)).mp heq).1),
      QueryCache.cacheQuery_of_ne right output (by
        intro heq
        exact hleafIndex ((CacheView.leafInput_eq_iff parameter candidate
          leafIndex (rightEndpoints candidate) (rightEndpoints leafIndex)).mp heq).1)]
    exact hrel candidate

def chainEndpointDigit : Digit :=
  ⟨chainLength - 1, by decide⟩

end Xmss.Generic

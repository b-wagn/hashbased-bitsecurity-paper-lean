import Xmss.Proof.Generic.CacheQuerySupport
import Xmss.Proof.Generic.AdaptiveFreshTarget
import Xmss.Proof.Generic.MerkleQueryBound
import Xmss.Proof.Generic.ConcreteQueryBound
import Xmss.Proof.Generic.CausalTreeCoupling
import Xmss.Proof.Generic.CacheReplayEval
import Xmss.Proof.Generic.Direct.Structural
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-!
# Key-generation values are unpredictable

Every value of key generation is the output of a fresh oracle query, so it takes any fixed value
with probability at most `2^-128`: a tree node (`probEvent_rootTree_treeNode_le`) and a positive
chain value (`probEvent_rootTree_chainValue_le`), as replayed from the final key-generation cache.
-/

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.Checksum.HiddenSibling

/-- The probability of one digest value. -/
noncomputable abbrev digestInverse : ℝ≥0∞ := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹

/-- An event that implies, on the support, an event of the first part of a bind. -/
theorem probEvent_bind_le_of_imp {α β : Type} (head : ProbComp α) (tail : α → ProbComp β)
    (event : β → Prop) (headEvent : α → Prop)
    (himp : ∀ a ∈ support head, ∀ b ∈ support (tail a), event b → headEvent a) :
    Pr[event | head >>= tail] ≤ Pr[headEvent | head] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support head
  · by_cases hevent : headEvent a
    · rw [if_pos hevent]
      exact mul_le_of_le_one_right' probEvent_le_one
    · rw [if_neg hevent]
      have hzero : Pr[event | tail a] = 0 :=
        probEvent_eq_zero fun b hb hb' => hevent (himp a ha b hb hb')
      rw [hzero, mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul]
    exact zero_le

/-- An injective image of a value with small point probabilities has small point probabilities. -/
theorem probEvent_injective_comp_le {α β γ : Type} (computation : ProbComp α) (value : α → β)
    (encode : β → γ) (hencode : Function.Injective encode) (bound : ℝ≥0∞)
    (hbound : ∀ target, Pr[fun a => value a = target | computation] ≤ bound) (target : γ) :
    Pr[fun a => encode (value a) = target | computation] ≤ bound := by
  rcases Classical.em (∃ preimage, encode preimage = target) with hrange | hrange
  · obtain ⟨preimage, rfl⟩ := hrange
    simpa only [hencode.eq_iff] using hbound preimage
  · push Not at hrange
    rw [probEvent_eq_zero fun a _ ha => hrange _ ha]
    exact zero_le

theorem tsum_probOutput_mul_le_of_mem_support {β : Type} (computation : ProbComp β)
    (f : β → ℝ≥0∞) (bound : ℝ≥0∞) (h : ∀ x ∈ support computation, f x ≤ bound) :
    ∑' x, Pr[= x | computation] * f x ≤ bound :=
  calc
    _ ≤ ∑' x, Pr[= x | computation] * bound := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      by_cases hx : x ∈ support computation
      · exact mul_le_mul' le_rfl (h x hx)
      · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
    _ = (∑' x, Pr[= x | computation]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := by gcongr; exact tsum_probOutput_le_one
    _ = bound := one_mul _

/-! ## A fresh final query -/

theorem probEvent_tweakableHash_fresh (parameter : PublicParameter) (domain : Generic.HashDomain)
    (payload : HashInput) (cache : QueryCache HashSpec)
    (hnone : cache (Generic.tweakableHashInput parameter domain payload) = none) (target : Digest) :
    Pr[fun result => result.1 = target |
      (simulateQ randomOracle
        (Generic.Hashing.tweakableHash parameter domain payload : OracleComp HashSpec Digest)).run
          cache] = digestInverse := by
  have hrun :
      (simulateQ randomOracle
        (Generic.Hashing.tweakableHash parameter domain payload : OracleComp HashSpec Digest)).run
          cache =
      (fun output : Digest =>
        (output,
          cache.cacheQuery (Generic.tweakableHashInput parameter domain payload) output)) <$>
        ($ᵗ Digest) := by
    simp only [Generic.Hashing.tweakableHash, Generic.Hashing.oracleHash]
    rw [show (simulateQ randomOracle
        (HasQuery.query (spec := HashSpec) (m := OracleComp HashSpec)
          (Generic.tweakableHashInput parameter domain payload))).run cache =
        (randomOracle (spec := HashSpec) (Generic.tweakableHashInput parameter domain payload)).run cache
      from by simp [HasQuery.query]]
    rw [QueryImpl.withCaching_run_none _ hnone]
    simp [uniformSampleImpl, map_eq_bind_pure_comp]
  rw [hrun, probEvent_map]
  exact RandomOracle.uniform_eq_probability target

theorem probEvent_bind_tweakableHash_le {β : Type} (head : OracleComp HashSpec β)
    (parameter : PublicParameter) (domain : Generic.HashDomain) (payload : β → HashInput)
    (cache : QueryCache HashSpec)
    (hhead : head.IsQueryBoundP (AtHashAddress parameter domain) 0)
    (hcache : ∀ input, AtHashAddress parameter domain input → cache input = none)
    (target : Digest) :
    Pr[fun result => result.1 = target |
      (simulateQ randomOracle (head >>= fun value =>
        (Generic.Hashing.tweakableHash parameter domain (payload value) :
          OracleComp HashSpec Digest))).run cache] ≤ digestInverse := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun headResult hheadResult => ?_
  have hinput := atHashAddress_tweakableHashInput_iff parameter domain domain
    (payload headResult.1)
  have hnone : headResult.2 (Generic.tweakableHashInput parameter domain (payload headResult.1)) =
      none := by
    refine CacheReplay.cache_none_of_zero_query_bound head _ cache headResult.2
      headResult.1 (OracleComp.IsQueryBoundP.of_imp (fun input hinput' => ?_) hhead) (hcache _ (hinput.2 rfl)) hheadResult
    rw [hinput']
    exact hinput.2 rfl
  exact (probEvent_tweakableHash_fresh parameter domain _ _ hnone target).le

/-! ## Chain values and tree nodes from the empty cache -/

theorem probEvent_chainWalk_le (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (steps : ℕ) (hpositive : 0 < steps) (hsteps : steps ≤ chainLength - 1)
    (value : Digest) (target : Digest) :
    Pr[fun result => result.1 = target |
      (simulateQ randomOracle
        (Generic.Wots.chainWalk parameter leafIndex chain 0 steps value :
          OracleComp HashSpec Digest)).run ∅] ≤ digestInverse := by
  obtain ⟨previous, rfl⟩ : ∃ previous, steps = previous + 1 := ⟨steps - 1, by omega⟩
  have hprevious : 0 + previous < chainLength - 1 := by omega
  have hwalk : (Generic.Wots.chainWalk parameter leafIndex chain 0 (previous + 1) value :
      OracleComp HashSpec Digest) =
      (Generic.Wots.chainWalk parameter leafIndex chain 0 previous value :
        OracleComp HashSpec Digest) >>= fun current =>
        (Generic.Hashing.tweakableHash parameter
          (.chain leafIndex chain ⟨0 + previous, hprevious⟩) (Generic.bytesLE 16 current) :
          OracleComp HashSpec Digest) := by
    rw [Generic.Wots.chainWalk]
    simp only [hprevious, ↓reduceDIte, Generic.Hashing.chainHash]
  rw [hwalk]
  refine probEvent_bind_tweakableHash_le _ parameter _ _ ∅ ?_ (fun _ _ => rfl) target
  apply Wots.chainWalk_queryBound_zero_of_avoids
  intro offset hoffset _ hdomain
  simp only [Generic.HashDomain.chain.injEq, Fin.mk.injEq] at hdomain
  omega

theorem probEvent_treeNode_le (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : ℕ) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) (target : Digest) :
    Pr[fun result => result.1 = target |
      (simulateQ randomOracle
        (Generic.Merkle.treeNode parameter secret levels node : OracleComp HashSpec Digest)).run ∅] ≤
      digestInverse := by
  cases levels with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      unfold Generic.Merkle.leafAt
      exact probEvent_bind_tweakableHash_le _ parameter _ _ ∅
        (Wots.oneTimePublicKey_queryBound_zero_leafAddress parameter secret node node)
        (fun _ _ => rfl) target
  | succ levels =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      have hchild : ∀ right : Bool,
          (Generic.Merkle.treeNode parameter secret levels (Generic.Merkle.childNode node right) :
            OracleComp HashSpec Digest).IsQueryBoundP
            (AtHashAddress parameter (.merkle ⟨levels, hlevel⟩ node)) 0 := by
        intro right
        have h := Merkle.treeNode_queryBound_merkleAddress parameter secret ⟨levels, hlevel⟩
          node levels (Generic.Merkle.childNode node right) (Nat.le_of_succ_le hlevels)
          (childNode_subtreeValid levels node right hvalid)
        simpa [MerkleAddressInSubtree] using h
      have htree : (Generic.Merkle.treeNode parameter secret (levels + 1) node :
          OracleComp HashSpec Digest) =
          (do
            let left ← (Generic.Merkle.treeNode parameter secret levels (Generic.Merkle.childNode node false) :
              OracleComp HashSpec Digest)
            let right ← (Generic.Merkle.treeNode parameter secret levels
              (Generic.Merkle.childNode node true) : OracleComp HashSpec Digest)
            pure (left, right)) >>= fun children =>
            (Generic.Hashing.tweakableHash parameter (.merkle ⟨levels, hlevel⟩ node)
              (Generic.Hashing.nodePayload children.1 children.2) : OracleComp HashSpec Digest) := by
        rw [Merkle.treeNode_succ_eq]
        simp only [hlevel, ↓reduceDIte, Generic.Hashing.nodeHash, bind_assoc, pure_bind]
      rw [htree]
      refine probEvent_bind_tweakableHash_le _ parameter _ _ ∅ ?_ (fun _ _ => rfl) target
      refine OracleComp.isQueryBoundP_bind (m := 0) (hchild false) fun _ _ => ?_
      refine OracleComp.isQueryBoundP_bind (m := 0) (hchild true) fun _ _ => ?_
      simp

/-! ## Values replayed from the key-generation cache -/

theorem probEvent_rootTree_treeNode_le (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : ℕ) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) (target : Digest) :
    Pr[fun result => CacheReplay.treeNode result.2 parameter secret levels node = target |
      (simulateQ randomOracle
        (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅] ≤ digestInverse := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_rootTree_run_eq_treeNode_then_rootTree parameter secret levels node hlevels
      hvalid ∅)]
  refine (probEvent_bind_le_of_imp _ _ _ (fun warm => warm.1 = target) ?_).trans
    (probEvent_treeNode_le parameter secret levels node hlevels hvalid target)
  intro warm hwarm result hresult hevent
  have hle := CacheReplay.randomOracle_cache_le _ warm.2 result hresult
  have heval := CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Generic.Merkle.treeNode parameter secret levels node : OracleComp HashSpec Digest)
    ∅ warm.2 result.2 warm.1 hwarm hle
  rw [CacheReplay.eval_treeNode] at heval
  rw [← heval]
  exact hevent

theorem probEvent_rootTree_chainValue_le (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) (chain : ChainIndex)
    (steps : ℕ) (hpositive : 0 < steps) (hsteps : steps ≤ chainLength - 1) (target : Digest) :
    Pr[fun result => Wots.walk
        (CacheView.chainStep result.2 parameter leafIndex chain) 0 steps
        (secret leafIndex chain) = target |
      (simulateQ randomOracle
        (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅] ≤ digestInverse := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_rootTree_run_eq_chainWalk_then_rootTree parameter secret leafIndex chain steps
      hsteps ∅)]
  refine (probEvent_bind_le_of_imp _ _ _ (fun warm => warm.1 = target) ?_).trans
    (probEvent_chainWalk_le parameter leafIndex chain steps hpositive hsteps _ target)
  intro warm hwarm result hresult hevent
  have hle := CacheReplay.randomOracle_cache_le _ warm.2 result hresult
  have heval := CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Generic.Wots.chainWalk parameter leafIndex chain 0 steps (secret leafIndex chain) :
      OracleComp HashSpec Digest) ∅ warm.2 result.2 warm.1 hwarm hle
  rw [CacheReplay.eval_chainWalk] at heval
  rw [← heval]
  exact hevent

end Xmss.Checksum.HiddenSibling

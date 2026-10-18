import XmssSecurity.Proof.Checksum.NoSign.FreshOutput
import XmssSecurity.Proof.Generic.MerkleQueryPresence
import XmssSecurity.Proof.Generic.QueryPresence
import XmssSecurity.Proof.Generic.ChainOraclePresampling
import XmssSecurity.Proof.Generic.CappedChain.KeygenUnaddressedCache
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-!
# A fixed input is rarely a key-generation input

For a fixed public parameter and a fixed hash input, the cache of key generation (from uniform
chain starts) contains that input with probability at most `2^-128`
(`probEvent_keygenTree_cached_le`): the key-generation cache has one input at each address, and
its payload contains a chain start, a chain value, a chain end, or a child node, each of which
is unpredictable (`FreshOutput.lean`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

/-! ## Uniform functions -/

/-- A uniform function is uniform at each point. -/
theorem probEvent_uniformFun_apply {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [Nonempty β] [SampleableType (α → β)] [SampleableType β] (a : α) (event : β → Prop) :
    Pr[fun f : α → β => event (f a) | $ᵗ (α → β)] = Pr[event | $ᵗ β] := by
  classical
  rw [probEvent_uniformSample, probEvent_uniformSample]
  let rest := {j // j ≠ a} → β
  have hfilter : (Finset.univ.filter fun f : α → β => event (f a)).card =
      (Finset.univ.filter event).card * Fintype.card rest := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_prod]
    refine Fintype.card_congr (((Equiv.funSplitAt a β).subtypeEquiv fun f => ?_).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := event)))
    rfl
  have htotal : Fintype.card (α → β) = Fintype.card β * Fintype.card rest := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (Equiv.funSplitAt a β)
  have hrest : (Fintype.card rest : ℝ≥0∞) ≠ 0 := by
    have : Nonempty rest := ⟨fun _ => Classical.arbitrary β⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [hfilter, htotal, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right _ _ hrest (ENNReal.natCast_ne_top _)

noncomputable local instance : SampleableType (LeafIndex → Generic.ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → Generic.ChainIndex → Digest)

noncomputable local instance : SampleableType (Generic.ChainIndex → Digest) :=
  SampleableType.ofFintype (Generic.ChainIndex → Digest)

theorem probEvent_sampleSecret_apply (leafIndex : LeafIndex) (chain : Generic.ChainIndex)
    (target : Digest) :
    Pr[fun secret => secret leafIndex chain = target | Generic.Concrete.sampleSecret] = digestInverse := by
  rw [Generic.Concrete.sampleSecret_eq]
  rw [probEvent_uniformFun_apply leafIndex (fun values : Generic.ChainIndex → Digest =>
      values chain = target)]
  rw [probEvent_uniformFun_apply chain (fun value : Digest => value = target),
    probEvent_eq_eq_probOutput, probOutput_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ digestBits := by simp
  rw [hcard]

/-! ## Inputs at an address -/

theorem eq_tweakableHashInput_of_atHashAddress (parameter : PublicParameter)
    (domain : Generic.HashDomain) (input : HashInput) (hinput : Generic.AtHashAddress parameter domain input) :
    input = Generic.tweakableHashInput parameter domain (input.drop 32) := by
  unfold Generic.AtHashAddress at hinput
  unfold Generic.tweakableHashInput
  rw [← hinput, List.take_append_drop]

/-- The key-generation tree computation never caches an input at no address. -/
theorem rootTree_cache_none_unaddressed (parameter : PublicParameter)
    (secret : LeafIndex → Generic.ChainIndex → Digest) (input : HashInput)
    (hinput : ¬ ∃ domain, Generic.AtHashAddress parameter domain input)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅)) :
    result.2 input = none := by
  apply Generic.Concrete.CacheReplay.cache_none_of_zero_query_bound _ input ∅ result.2 result.1 _ rfl
    hresult
  apply (Generic.CappedChain.Concrete.treeNode_queryBound_zero_unaddressed parameter secret
    treeHeight Generic.Concrete.rootNode).of_imp
  intro candidate heq
  subst candidate
  exact hinput

theorem rootTree_cache_none_of_zero_bound (parameter : PublicParameter)
    (secret : LeafIndex → Generic.ChainIndex → Digest) (domain : Generic.HashDomain) (input : HashInput)
    (hinput : Generic.AtHashAddress parameter domain input)
    (hbound : (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP (Generic.AtHashAddress parameter domain) 0)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅)) :
    result.2 input = none := by
  apply Generic.Concrete.CacheReplay.cache_none_of_zero_query_bound _ input ∅ result.2 result.1 _ rfl
    hresult
  apply hbound.of_imp
  intro candidate heq
  subst candidate
  exact hinput

/-! ## The bound for one secret, away from the chain starts -/

theorem probEvent_rootTree_cached_le (parameter : PublicParameter)
    (secret : LeafIndex → Generic.ChainIndex → Digest) (input : HashInput)
    (hstart : ∀ leafIndex chain (hstep : 0 < chainLength - 1),
      ¬ Generic.AtHashAddress parameter (.chain leafIndex chain ⟨0, hstep⟩) input) :
    Pr[fun result : Digest × QueryCache HashSpec => result.2 input ≠ none |
      (simulateQ randomOracle
        (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
          OracleComp HashSpec Digest)).run ∅] ≤ digestInverse := by
  let tree := (simulateQ randomOracle
    (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  rcases Classical.em (∃ domain, Generic.AtHashAddress parameter domain input) with
    ⟨domain, hdomain⟩ | hunaddressed
  swap
  · rw [probEvent_eq_zero fun result hresult hcached =>
      hcached (rootTree_cache_none_unaddressed parameter secret input hunaddressed result hresult)]
    exact zero_le
  have hinput := eq_tweakableHashInput_of_atHashAddress parameter domain input hdomain
  cases domain with
  | chain leafIndex chain step =>
      have hpositive : 0 < step.val := by
        rcases Nat.eq_zero_or_pos step.val with hzero | hpositive
        · exfalso
          apply hstart leafIndex chain (by omega)
          have hstepEq : step = ⟨0, by omega⟩ := Fin.ext hzero
          rw [← hstepEq]
          exact hdomain
        · exact hpositive
      have himp : ∀ result ∈ support tree, result.2 input ≠ none →
          Generic.Concrete.CacheView.chainInput parameter leafIndex chain step
            (Generic.Wots.walk (Generic.Concrete.CacheView.chainStep result.2 parameter leafIndex chain) 0
              step.val (secret leafIndex chain)) = input := by
        intro result hresult hcached
        obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcached
        obtain ⟨honestOutput, hhonest⟩ :=
          Generic.Concrete.CacheReplay.rootTree_chain_query_cached parameter secret leafIndex chain step
            result.1 result.2 hresult
        exact Generic.Concrete.CacheReplay.rootTree_cache_unique_chainAddress parameter secret result.1
          result.2 hresult leafIndex chain step _ _ honestOutput output
          (by simp [Generic.Concrete.CacheView.chainInput]) hdomain hhonest houtput
      calc
        _ ≤ Pr[fun result : Digest × QueryCache HashSpec =>
              Generic.Concrete.CacheView.chainInput parameter leafIndex chain step
                (Generic.Wots.walk (Generic.Concrete.CacheView.chainStep result.2 parameter leafIndex chain) 0
                  step.val (secret leafIndex chain)) = input | tree] :=
          probEvent_mono fun result hresult hcached => himp result hresult hcached
        _ ≤ digestInverse :=
          probEvent_injective_comp_le tree _ _
            (Generic.Concrete.CacheView.chainInput_injective parameter leafIndex chain step) _
            (probEvent_rootTree_chainValue_le parameter secret leafIndex chain step.val
              hpositive (by omega)) input
  | leaf leafIndex =>
      have himp : ∀ result ∈ support tree, result.2 input ≠ none →
          Generic.Concrete.CacheView.leafInput parameter leafIndex
            (Generic.Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret leafIndex) =
            input := by
        intro result hresult hcached
        obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcached
        obtain ⟨honestOutput, hhonest⟩ :=
          Generic.Concrete.CacheReplay.rootTree_leaf_query_cached parameter secret leafIndex
            result.1 result.2 hresult
        exact Generic.Concrete.CacheReplay.rootTree_cache_unique_leafAddress parameter secret result.1
          result.2 hresult leafIndex _ _ honestOutput output
          (by simp [Generic.Concrete.CacheView.leafInput]) hdomain hhonest houtput
      let firstChain : Generic.ChainIndex := ⟨0, Generic.Code.numChains_pos⟩
      calc
        _ ≤ Pr[fun result : Digest × QueryCache HashSpec =>
              Generic.Concrete.CacheView.leafInput parameter leafIndex
                (Generic.Concrete.CacheReplay.oneTimePublicKey result.2 parameter secret leafIndex) =
                input | tree] :=
          probEvent_mono fun result hresult hcached => himp result hresult hcached
        _ ≤ digestInverse := by
          refine probEvent_injective_comp_le tree _ _
            (Generic.Concrete.CacheView.leafInput_injective parameter leafIndex) _ (fun target => ?_)
            input
          calc
            _ ≤ Pr[fun result : Digest × QueryCache HashSpec =>
                  Generic.Wots.walk (Generic.Concrete.CacheView.chainStep result.2 parameter leafIndex firstChain)
                    0 (chainLength - 1) (secret leafIndex firstChain) = target firstChain |
                  tree] :=
              probEvent_mono fun result _ hequal => by
                rw [← hequal]
                rfl
            _ ≤ digestInverse :=
              probEvent_rootTree_chainValue_le parameter secret leafIndex firstChain _
                (by simp [chainLength, winternitzBits]) le_rfl _
  | merkle level node =>
      by_cases hnode : node.val < 2 ^ (treeHeight - (level.val + 1))
      · have hparentValid : Generic.TreeSubtreeValid (level.val + 1) node := by
          unfold Generic.TreeSubtreeValid lifetime
          have hlevel := level.isLt
          calc
            (node.val + 1) * 2 ^ (level.val + 1) ≤
                2 ^ (treeHeight - (level.val + 1)) * 2 ^ (level.val + 1) :=
              Nat.mul_le_mul_right _ hnode
            _ = 2 ^ treeHeight := by
              rw [← pow_add]
              congr 1
              omega
        have himp : ∀ result ∈ support tree, result.2 input ≠ none →
            (fun children : Digest × Digest =>
              Generic.Concrete.CacheView.merkleInput parameter level node children.1 children.2)
              (Generic.Concrete.CacheReplay.treeNode result.2 parameter secret level.val
                  (Generic.Concrete.childNode node false),
                Generic.Concrete.CacheReplay.treeNode result.2 parameter secret level.val
                  (Generic.Concrete.childNode node true)) = input := by
          intro result hresult hcached
          obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcached
          obtain ⟨honestOutput, hhonest⟩ :=
            Generic.Concrete.CacheReplay.rootTree_merkle_query_cached parameter secret level node hnode
              result.1 result.2 result.2 hresult le_rfl
          exact Generic.Concrete.CacheReplay.rootTree_cache_unique_merkleAddress parameter secret
            result.1 result.2 hresult level node _ _ honestOutput output
            (by simp [Generic.Concrete.CacheView.merkleInput]) hdomain hhonest houtput
        have hinjective : Function.Injective fun children : Digest × Digest =>
            Generic.Concrete.CacheView.merkleInput parameter level node children.1 children.2 := by
          intro left right heq
          apply Generic.Concrete.nodePayload_injective
          exact Generic.payload_eq_of_tweakableHashInput_eq parameter (.merkle level node) heq
        calc
          _ ≤ Pr[fun result : Digest × QueryCache HashSpec =>
                (fun children : Digest × Digest =>
                  Generic.Concrete.CacheView.merkleInput parameter level node children.1 children.2)
                  (Generic.Concrete.CacheReplay.treeNode result.2 parameter secret level.val
                      (Generic.Concrete.childNode node false),
                    Generic.Concrete.CacheReplay.treeNode result.2 parameter secret level.val
                      (Generic.Concrete.childNode node true)) = input | tree] :=
            probEvent_mono fun result hresult hcached => himp result hresult hcached
          _ ≤ digestInverse := by
            refine probEvent_injective_comp_le tree _ _ hinjective _ (fun target => ?_) input
            calc
              _ ≤ Pr[fun result : Digest × QueryCache HashSpec =>
                    Generic.Concrete.CacheReplay.treeNode result.2 parameter secret level.val
                      (Generic.Concrete.childNode node false) = target.1 | tree] :=
                probEvent_mono fun result _ hequal => by rw [← hequal]
              _ ≤ digestInverse :=
                probEvent_rootTree_treeNode_le parameter secret level.val _
                  (by have := level.isLt; omega)
                  (Generic.childNode_subtreeValid level.val node false hparentValid) target.1
      · rw [probEvent_eq_zero fun result hresult hcached => hcached
          (rootTree_cache_none_of_zero_bound parameter secret _ input hdomain
            (by
              have h := Generic.Concrete.treeNode_queryBound_merkleAddress parameter secret level node
                treeHeight Generic.Concrete.rootNode le_rfl
                (by unfold Generic.TreeSubtreeValid Generic.Concrete.rootNode lifetime; norm_num)
              have hnot : ¬ Generic.MerkleAddressInSubtree level node treeHeight Generic.Concrete.rootNode := by
                rintro ⟨_, _, hcover⟩
                apply hnode
                simpa [Generic.Concrete.rootNode] using hcover
              simpa [hnot] using h)
            result hresult)]
        exact zero_le
  | encoding leafIndex =>
      rw [probEvent_eq_zero fun result hresult hcached => hcached
        (rootTree_cache_none_of_zero_bound parameter secret _ input hdomain
          (Generic.Concrete.treeNode_queryBound_zero_encodingAddress parameter secret leafIndex
            treeHeight Generic.Concrete.rootNode) result hresult)]
      exact zero_le

/-! ## Including the chain starts -/

/-- The parameter fixed, the chain starts uniform: the key-generation cache contains a fixed
input with probability at most `2^-128`. -/
theorem probEvent_keygenTree_cached_le (parameter : PublicParameter) (input : HashInput) :
    Pr[fun result : (LeafIndex → Generic.ChainIndex → Digest) × (Digest × QueryCache HashSpec) =>
        result.2.2 input ≠ none |
      do
        let secret ← Generic.Concrete.sampleSecret
        let tree ← (simulateQ randomOracle
          (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
            OracleComp HashSpec Digest)).run ∅
        pure (secret, tree)] ≤ digestInverse := by
  rcases Classical.em (∃ leafIndex chain, ∃ hstep : 0 < chainLength - 1,
      Generic.AtHashAddress parameter (.chain leafIndex chain ⟨0, hstep⟩) input) with
    ⟨leafIndex, chain, hstep, hdomain⟩ | hstart
  · -- A chain start: the input is cached exactly when its payload is that start.
    have hinput := eq_tweakableHashInput_of_atHashAddress parameter _ input hdomain
    calc
      _ ≤ Pr[fun secret : LeafIndex → Generic.ChainIndex → Digest =>
            Generic.Concrete.CacheView.chainInput parameter leafIndex chain ⟨0, hstep⟩
              (secret leafIndex chain) = input | Generic.Concrete.sampleSecret] := by
        refine probEvent_bind_le_of_imp _ _ _ _ fun secret _ result hresult hcached => ?_
        rw [support_bind] at hresult
        simp only [support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hresult
        obtain ⟨tree, htree, rfl⟩ := hresult
        obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hcached
        obtain ⟨honestOutput, hhonest⟩ :=
          Generic.Concrete.CacheReplay.rootTree_chain_query_cached parameter secret leafIndex chain
            ⟨0, hstep⟩ tree.1 tree.2 htree
        have heq := Generic.Concrete.CacheReplay.rootTree_cache_unique_chainAddress parameter secret
          tree.1 tree.2 htree leafIndex chain ⟨0, hstep⟩ _ _ honestOutput output
          (by simp [Generic.Concrete.CacheView.chainInput]) hdomain hhonest houtput
        simpa [Generic.Wots.walk] using heq
      _ ≤ digestInverse :=
        probEvent_injective_comp_le _ _ _
          (Generic.Concrete.CacheView.chainInput_injective parameter leafIndex chain ⟨0, hstep⟩) _
          (fun target => (probEvent_sampleSecret_apply leafIndex chain target).le) input
  · push Not at hstart
    rw [probEvent_bind_eq_tsum]
    refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun secret _ => ?_
    rw [bind_pure_comp, probEvent_map]
    exact probEvent_rootTree_cached_le parameter secret input fun leafIndex chain hstep =>
      hstart leafIndex chain hstep

end XmssSecurity.Checksum.NoSign

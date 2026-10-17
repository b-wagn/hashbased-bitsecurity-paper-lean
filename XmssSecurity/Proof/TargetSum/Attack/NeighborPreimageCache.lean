import XmssSecurity.Proof.TargetSum.Attack.NeighborSearch
import XmssSecurity.Proof.TargetSum.Attack.PreimageSearch

/-! The neighboring-encoding search leaves every chain address as key generation left it,
so the bounded predecessor search applies to a chain of the original signature. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Attack

open Concrete

def predecessorStep (encoding : Encoding) (lower : DecreasingChain encoding) : ChainStep :=
  ⟨(encoding lower.1).val - 1, by
    have hpositive := lower.2
    have hbound := (encoding lower.1).isLt
    omega⟩

@[simp] theorem predecessorStep_add_one (encoding : Encoding) (lower : DecreasingChain encoding) :
    (predecessorStep encoding lower).val + 1 = (encoding lower.1).val := by
  have hpositive := lower.2
  simp only [predecessorStep]
  omega

theorem encodingInput_ne_chainInput (parameter : PublicParameter)
    (signingLeaf : LeafIndex) (message : Message) (randomness : Randomness)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    CacheView.encodingInput parameter signingLeaf (message, randomness) ≠
      CacheView.chainInput parameter leafIndex chain step value := by
  intro heq
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
  contradiction

theorem precomputedCappedSign_preserves_chainInput
    (secretKey : SecretKey) (signingLeaf : LeafIndex) (message : Message)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign secretKey signingLeaf message)).run initialCache))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    finalCache (CacheView.chainInput secretKey.parameter leafIndex chain step value) =
      initialCache (CacheView.chainInput secretKey.parameter leafIndex chain step value) := by
  rw [precomputedCappedSign] at hmem
  exact precomputedSignBoundedAttempts_preserves_unqueriedInput _ _ _ _ _
    (fun randomness => encodingInput_ne_chainInput _ _ _ randomness _ _ _ _)
    initialCache finalCache result hmem

theorem findEncodingNeighbor_preserves_chainInput
    (parameter : PublicParameter) (searchLeaf : LeafIndex) (message : Message) (encoding : Encoding)
    (initialCache finalCache : QueryCache HashSpec) (result : Option (ℕ × HashOutput))
    (hmem : (result, finalCache) ∈ support ((simulateQ randomOracle
      (findEncodingNeighbor parameter searchLeaf message encoding)).run initialCache))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest) :
    finalCache (CacheView.chainInput parameter leafIndex chain step value) =
      initialCache (CacheView.chainInput parameter leafIndex chain step value) := by
  apply findHash_preserves_unqueriedInput _ _ _ _ _ _ initialCache finalCache result hmem
  intro i _ _
  exact encodingInput_ne_chainInput parameter searchLeaf message _ leafIndex chain step value

theorem predecessorCache_after_neighborSearch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (signCache : QueryCache HashSpec)
    (hsign : (some signature, signCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (encoding : Encoding)
    (hreplay : signature = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      request.epoch signature.randomness encoding)
    (message : Message) (answer : Option (ℕ × HashOutput)) (searchCache : QueryCache HashSpec)
    (hsearch : (answer, searchCache) ∈ support ((simulateQ randomOracle
      (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache))
    (lower : DecreasingChain encoding) :
    ∃ genuine,
      (∃ output, searchCache (CacheView.chainInput keyResult.1.2.parameter request.epoch lower.1
          (predecessorStep encoding lower) genuine) = some output ∧
        truncateHash output = signature.chainValue lower.1) ∧
      ∀ value, value ≠ genuine →
        searchCache (CacheView.chainInput keyResult.1.2.parameter request.epoch lower.1
          (predecessorStep encoding lower) value) = none := by
  have hagree : ∀ value, searchCache (CacheView.chainInput keyResult.1.2.parameter request.epoch
      lower.1 (predecessorStep encoding lower) value) =
      keyResult.2 (CacheView.chainInput keyResult.1.2.parameter request.epoch
        lower.1 (predecessorStep encoding lower) value) := by
    intro value
    rw [findEncodingNeighbor_preserves_chainInput _ _ _ _ _ _ _ hsearch,
      precomputedCappedSign_preserves_chainInput _ _ _ _ _ _ hsign]
  obtain ⟨previous, output, hprevious, hcached, htarget⟩ :=
    precomputedKeygen_cache_has_chainValue_preimage keyResult hkey request.epoch lower.1
      (encoding lower.1) lower.2
  have heq : previous = predecessorStep encoding lower := by
    apply Fin.ext
    have hstep := predecessorStep_add_one encoding lower
    omega
  subst previous
  refine ⟨Wots.walk (CacheView.chainStep keyResult.2 keyResult.1.2.parameter request.epoch lower.1)
    0 (predecessorStep encoding lower).val (keyResult.1.2.chainStart request.epoch lower.1),
    ⟨output, ?_, ?_⟩, ?_⟩
  · rw [hagree]
    exact hcached
  · rw [hreplay]
    exact htarget
  · intro value hne
    rw [hagree]
    exact precomputedKeygen_cache_chainInput_eq_none_of_ne keyResult hkey request.epoch lower.1
      (predecessorStep encoding lower) value hne

theorem randomDigestPreimage_success_after_neighborSearch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (signCache : QueryCache HashSpec)
    (hsign : (some signature, signCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (encoding : Encoding)
    (hreplay : signature = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      request.epoch signature.randomness encoding)
    (message : Message) (answer : Option (ℕ × HashOutput)) (searchCache : QueryCache HashSpec)
    (hsearch : (answer, searchCache) ∈ support ((simulateQ randomOracle
      (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache))
    (lower : DecreasingChain encoding) :
    2 / 17 ≤ Pr[fun result => result.2.1 ≠ none |
      randomDigestPreimage (CacheView.chainInput keyResult.1.2.parameter request.epoch lower.1
        (predecessorStep encoding lower)) (signature.chainValue lower.1) searchCache] := by
  obtain ⟨genuine, hhit, hfresh⟩ := predecessorCache_after_neighborSearch keyResult hkey request
    signature signCache hsign encoding hreplay message answer searchCache hsearch lower
  exact randomDigestPreimage_success _ (CacheView.chainInput_injective _ _ _ _) _ genuine _ hhit hfresh

/-- info: 'XmssSecurity.TargetSum.Attack.randomDigestPreimage_success_after_neighborSearch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomDigestPreimage_success_after_neighborSearch

end XmssSecurity.TargetSum.Attack

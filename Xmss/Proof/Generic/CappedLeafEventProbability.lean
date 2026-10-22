import Xmss.Proof.Generic.CappedDetailedQueryPresence
import Xmss.Proof.Generic.CappedSigningLogReplay
import Xmss.Proof.Generic.LeafTargetInput

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic.CappedLeaf

variable [Code]

/-- Map a leaf input to the honest leaf input fixed by key generation at the same leaf index. -/
noncomputable def keygenLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ leafIndex endpoints,
      input = CacheView.leafInput secretKey.parameter leafIndex endpoints then
    CacheView.leafInput secretKey.parameter h.choose
      (CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart h.choose)
  else input

@[simp]
theorem keygenLeafTargetInput_leafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenLeafTargetInput secretKey cache
      (CacheView.leafInput secretKey.parameter leafIndex endpoints) =
      CacheView.leafInput secretKey.parameter leafIndex
        (CacheReplay.oneTimePublicKey cache secretKey.parameter
          secretKey.chainStart leafIndex) := by
  unfold keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨chosenEndpoints, hinput⟩ := h.choose_spec
    have hleafIndex : h.choose = leafIndex := by
      have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
        (hinput.trans rfl)
      simp only [HashDomain.leaf.injEq] at hdomain
      exact hdomain.symm
    rw [hleafIndex]
  · rename_i h
    exfalso
    exact h ⟨leafIndex, endpoints, rfl⟩

attribute [irreducible] keygenLeafTargetInput

theorem detailedGameAfterKeygen_keys_eq
    (adversary : Adversary) (publicKey : PublicKey) (secretKey : SecretKey)
    (initialCache : QueryCache HashSpec) (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen precomputedScheme adversary publicKey secretKey)).run
          initialCache)) :
    execution.1.publicKey = publicKey ∧ execution.1.secretKey = secretKey := by
  unfold detailedGameAfterKeygen at hmem
  simp only at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  exact ⟨rfl, rfl⟩

/-- A successful detailed execution caches the forged leaf for its uniquely decoded encoding. -/
theorem detailed_execution_verified_leaf_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hgame : execution ∈ support (detailedGameWithCache precomputedScheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : CacheView.decodedEncoding execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness) =
        some encoding) :
    ∃ output, execution.2
      (CacheView.leafInput execution.1.secretKey.parameter execution.1.forgery.epoch
        (recoveredEndpoints
          (fun chain => CacheView.chainStep execution.2
            execution.1.secretKey.parameter execution.1.forgery.epoch chain)
          encoding execution.1.forgery.signature.chainValue)) = some output := by
  obtain ⟨actualEncoding, output, hactualDecode, hcached⟩ :=
    capped_detailed_execution_verified_leaf_cached adversary execution hgame hverified
  have hencoding : actualEncoding = encoding := by
    rw [hdecode] at hactualDecode
    exact Option.some.inj hactualDecode.symm
  subst actualEncoding
  exact ⟨output, hcached⟩

theorem afterKeygen_execution_mem_detailedGame
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen precomputedScheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2)) :
    execution ∈ support (detailedGameWithCache precomputedScheme adversary) := by
  unfold detailedGameWithCache detailedGameCore
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨keyResult, hkeygen, hafter⟩

end Xmss.Generic.CappedLeaf

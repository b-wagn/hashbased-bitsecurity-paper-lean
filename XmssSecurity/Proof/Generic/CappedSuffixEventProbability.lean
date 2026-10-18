import XmssSecurity.Proof.Generic.CappedLeafEventProbability
import XmssSecurity.Proof.Generic.VerificationChainQuery

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic.CappedSuffix

variable [Code]

theorem detailed_execution_verified_chain_query_cached_as
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support (detailedGameWithCache Concrete.scheme adversary))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : Concrete.CacheView.decodedEncoding execution.2 execution.1.secretKey.parameter
        execution.1.forgery.epoch
        (execution.1.forgery.message, execution.1.forgery.signature.randomness) =
        some encoding)
    (chain : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (encoding chain).val) :
    ∃ output, execution.2
      (Concrete.CacheView.chainInput execution.1.secretKey.parameter
        execution.1.forgery.epoch chain
        ⟨(encoding chain).val + offset, by omega⟩
        (Wots.walk
          (Concrete.CacheView.chainStep execution.2 execution.1.secretKey.parameter
            execution.1.forgery.epoch chain)
          (encoding chain).val offset (execution.1.forgery.signature.chainValue chain))) =
        some output := by
  have hparameter :=
    (capped_detailed_execution_key_components_consistent adversary execution hmem).1
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  cases hfinal
  simp only at hparameter hverified hdecode ⊢
  subst verified
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.epoch forgery.message forgery.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.epoch forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  have hdecodePublic : Concrete.CacheView.decodedEncoding finalCache publicKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness) = some encoding := by
    rw [hparameter]
    exact hdecode
  rw [← hparameter]
  exact Concrete.CacheReplay.verify_true_chain_query_cached_as_in_largerCache publicKey
    forgery.epoch forgery.message forgery.signature encoding chain offset hoffset
    adversaryCache finalCache finalCache hverify hdecodePublic le_rfl

theorem Wots.walk_signChain_eq_honest (step : Nat → Digest → Digest)
    (digit : Digit) (offset : Nat) (secret : Digest) :
    Wots.walk step digit.val offset (Wots.signChain step digit secret) =
      Wots.walk step 0 (digit.val + offset) secret := by
  simpa only [Wots.signChain, zero_add] using
    (Wots.walk_add step 0 digit.val offset secret).symm

noncomputable def keygenChainTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ address : LeafIndex × ChainIndex × ChainStep, ∃ value,
      input = Concrete.CacheView.chainInput secretKey.parameter address.1
        address.2.1 address.2.2 value then
    let address := h.choose
    Concrete.CacheView.chainInput secretKey.parameter address.1 address.2.1 address.2.2
      (Wots.walk
        (Concrete.CacheView.chainStep cache secretKey.parameter address.1 address.2.1)
        0 address.2.2.val (secretKey.chainStart address.1 address.2.1))
  else input

@[simp]
theorem keygenChainTargetInput_chainInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    keygenChainTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
      Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step
        (Wots.walk (Concrete.CacheView.chainStep cache secretKey.parameter leafIndex chain)
          0 step.val (secretKey.chainStart leafIndex chain)) := by
  unfold keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨chosenValue, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      (hinput.trans rfl)
    simp only [HashDomain.chain.injEq] at hdomain
    rcases hdomain with ⟨hleafIndex, hchain, hstep⟩
    dsimp only
    rw [← hleafIndex, ← hchain, ← hstep]
  · rename_i h
    exfalso
    exact h ⟨(leafIndex, chain, step), value, rfl⟩

attribute [irreducible] keygenChainTargetInput

end XmssSecurity.Generic.CappedSuffix

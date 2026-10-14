import XmssSecurity.Proof.Direct.Deciding

/-!
# Orientation of the deciding path

For an execution of `detailedGameAfterKeygen` split into the adversary phase (cache `C_k → C_v`)
and the verification phase (cache `C_v → C_f`): a winning run without the encoding event, without
a revealed deciding chain value and without an adversary-phase structural collision exhibits a
fresh collision during verification whose witness lies on the deciding path
(`decidingTargetInput`).
-/

open OracleComp OracleSpec

namespace XmssSecurity.Deciding

open Concrete

/-! ### The two phases after key generation -/

noncomputable def adversaryPhase (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : SecretKey) : OracleComp OracleWorld (Forgery × QueryLog SigningSpec) :=
  (simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
    (adversary.main publicKey)).run

noncomputable def verificationPhase (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) : OracleComp OracleWorld GameOutcome := do
  let verified ← Concrete.scheme.verify publicKey prefixResult.1.epoch prefixResult.1.message
    prefixResult.1.signature
  return ⟨publicKey, secretKey, prefixResult.1, prefixResult.2, verified⟩

theorem detailedGameAfterKeygen_eq_phases (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : SecretKey) :
    detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey =
      adversaryPhase adversary publicKey secretKey >>= verificationPhase publicKey secretKey := by
  rfl

/-- An execution of both phases is an execution of `detailedGameAfterKeygen`. -/
theorem afterKeygen_of_phases (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : SecretKey) (initialCache : QueryCache HashSpec)
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support
      ((simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run initialCache))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl (verificationPhase publicKey secretKey prefixResult.1)).run
        prefixResult.2)) :
    execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary publicKey secretKey)).run
          initialCache) := by
  rw [detailedGameAfterKeygen_eq_phases, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨prefixResult, hprefix, hafter⟩

/-- The verification phase keeps the keys, forgery and log, and runs the verifier. -/
theorem verificationPhase_support (publicKey : PublicKey) (secretKey : SecretKey)
    (prefixResult : Forgery × QueryLog SigningSpec) (initialCache : QueryCache HashSpec)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl (verificationPhase publicKey secretKey prefixResult)).run
        initialCache)) :
    execution.1.publicKey = publicKey ∧ execution.1.secretKey = secretKey ∧
      execution.1.forgery = prefixResult.1 ∧ execution.1.signingLog = prefixResult.2 ∧
      (execution.1.verified, execution.2) ∈ support
        ((simulateQ romImpl (Concrete.scheme.verify publicKey prefixResult.1.epoch
          prefixResult.1.message prefixResult.1.signature)).run initialCache) := by
  unfold verificationPhase at hafter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafter
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hafter
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  subst hfinal
  exact ⟨rfl, rfl, rfl, rfl, hverify⟩

/-! ### Collision witnesses on the deciding path -/

/-- A fresh collision after key generation whose witness is a deciding input: the witness is
cached at the end, was not cached after key generation, its structural target was, and both have
the same digest at the end. -/
def DecidingCollisionWitness (secretKey : SecretKey) (keygenCache finalCache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) : Prop :=
  ∃ input output targetOutput,
    IsDecidingInput secretKey.parameter leafIndex chain input ∧
    finalCache input = some output ∧ keygenCache input = none ∧
    keygenCache (keygenStructuralTargetInput secretKey keygenCache input) = some targetOutput ∧
    Concrete.CacheView.digestAt finalCache input =
      Concrete.CacheView.digestAt finalCache
        (keygenStructuralTargetInput secretKey keygenCache input)

theorem cache_eq_some_of_le {initialCache finalCache : QueryCache HashSpec}
    (hle : initialCache ≤ finalCache) {input : HashInput} {output : HashOutput}
    (hcache : initialCache input = some output) : finalCache input = some output :=
  hle hcache

/-- Split a deciding witness `C_k → C_f` along an intermediate cache `C_v`: either it is a
structural collision `C_k → C_v`, or a deciding collision `C_v → C_f`. -/
theorem decidingCollision_of_witness (secretKey : SecretKey)
    (keygenCache prefixCache finalCache : QueryCache HashSpec)
    (hkeygenLe : keygenCache ≤ prefixCache) (hprefixLe : prefixCache ≤ finalCache)
    (leafIndex : LeafIndex) (chain : ChainIndex)
    (hwitness : DecidingCollisionWitness secretKey keygenCache finalCache leafIndex chain)
    (hnoPrefix : ¬ Rom.AdaptiveFreshDigestCollisionWith keygenCache prefixCache
      (keygenStructuralTargetInput secretKey keygenCache)) :
    Rom.AdaptiveFreshDigestCollisionWith prefixCache finalCache
      (decidingTargetInput secretKey keygenCache leafIndex chain) := by
  obtain ⟨input, output, targetOutput, hdeciding, hfinal, hkeygen, htarget, hdigest⟩ := hwitness
  have htargetPrefix := cache_eq_some_of_le hkeygenLe htarget
  have htargetFinal := cache_eq_some_of_le hprefixLe htargetPrefix
  cases hprefix : prefixCache input with
  | some prefixOutput =>
      exfalso
      apply hnoPrefix
      refine ⟨input, prefixOutput, targetOutput, hprefix, hkeygen, htarget, ?_⟩
      have hfinal' := cache_eq_some_of_le hprefixLe hprefix
      rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hprefix,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some htargetPrefix]
      rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hfinal',
        Concrete.CacheView.digestAt_eq_of_cache_eq_some htargetFinal] at hdigest
      exact hdigest
  | none =>
      refine ⟨input, output, targetOutput, hfinal, hprefix, ?_, ?_⟩
      · rw [decidingTargetInput_eq_structural_of_isDecidingInput secretKey keygenCache leafIndex
          chain input hdeciding]
        exact htargetPrefix
      · rw [decidingTargetInput_eq_structural_of_isDecidingInput secretKey keygenCache leafIndex
          chain input hdeciding]
        exact hdigest

/-! ### Facts about the deciding chain -/

/-- Either every chain is trivial, or the deciding chain is not. -/
theorem decidingChain_trivial_or_not (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (forgedEnc : Encoding) :
    (∀ chain, ChainTrivial cache secretKey log forgery forgedEnc chain) ∨
      ¬ ChainTrivial cache secretKey log forgery forgedEnc
        (decidingChain cache secretKey log forgery forgedEnc) := by
  classical
  unfold decidingChain
  cases hfind : decidingChain? cache secretKey log forgery forgedEnc with
  | none =>
      left
      intro chain
      unfold decidingChain? at hfind
      rw [List.find?_eq_none] at hfind
      have := hfind chain (List.mem_finRange chain)
      simpa using this
  | some chain =>
      right
      unfold decidingChain? at hfind
      have := List.find?_some hfind
      simpa using this

/-- The deciding chain only depends on the signed encoding and the honest chain values. -/
theorem decidingChain_congr (cache cache' : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (forgedEnc : Encoding)
    (hsigned : signedEncoding cache secretKey.parameter log forgery.epoch =
      signedEncoding cache' secretKey.parameter log forgery.epoch)
    (hhonest : ∀ chain digit, honestChainValue cache secretKey forgery.epoch chain digit =
      honestChainValue cache' secretKey forgery.epoch chain digit) :
    decidingChain cache secretKey log forgery forgedEnc =
      decidingChain cache' secretKey log forgery forgedEnc := by
  classical
  have htrivial : ∀ chain, ChainTrivial cache secretKey log forgery forgedEnc chain ↔
      ChainTrivial cache' secretKey log forgery forgedEnc chain := by
    intro chain
    unfold ChainTrivial
    rw [hsigned, hhonest]
  unfold decidingChain decidingChain?
  congr 1
  apply List.find?_congr
  intro chain _
  simp only [htrivial]

theorem outcomeDecidingChain_eq (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (forgedEnc : Encoding)
    (hforged : forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some forgedEnc) :
    outcomeDecidingChain cache outcome =
      decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery forgedEnc := by
  unfold outcomeDecidingChain
  rw [hforged]

/-- `returnedAt` only reports signatures the signer returned at that leaf index. -/
theorem returned_of_returnedAt (log : QueryLog SigningSpec) (leafIndex : LeafIndex)
    (request : SignRequest) (signature : Signature)
    (hreturned : returnedAt log leafIndex = some (request, signature)) :
    SigningTranscript.Returned log request signature ∧ request.epoch = leafIndex := by
  unfold returnedAt at hreturned
  obtain ⟨entry, hmem, hentry⟩ := List.exists_of_findSome?_eq_some hreturned
  cases hsig : entry.2 with
  | none =>
      rw [hsig] at hentry
      cases hentry
  | some entrySignature =>
      rw [hsig] at hentry
      by_cases hepoch : entry.1.epoch = leafIndex
      · rw [if_pos hepoch] at hentry
        cases hentry
        exact ⟨⟨entry, hmem, rfl, hsig⟩, hepoch⟩
      · rw [if_neg hepoch] at hentry
        cases hentry

end XmssSecurity.Deciding

import XmssSecurity.Proof.Generic.Direct.Deciding

/-!
# Orientation of the deciding path

For an execution of `detailedGameAfterKeygen` split into the adversary phase (cache `C_k → C_v`)
and the verification phase (cache `C_v → C_f`): a winning run without the encoding event, without
a revealed deciding chain value and without an adversary-phase structural collision exhibits a
fresh collision during verification whose witness lies on the deciding path
(`decidingTargetInput`).
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

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

/-- A fresh collision across two cache extensions must occur in one of the extensions. -/
theorem adaptiveFreshCollision_split (initialCache prefixCache finalCache : QueryCache HashSpec)
    (target : HashInput → HashInput) (hfirst : initialCache ≤ prefixCache)
    (hsecond : prefixCache ≤ finalCache)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache target)
    (hnoPrefix : ¬ Rom.AdaptiveFreshDigestCollisionWith initialCache prefixCache target) :
    Rom.AdaptiveFreshDigestCollisionWith prefixCache finalCache target := by
  obtain ⟨input, output, targetOutput, hfinal, hinitial, htarget, hdigest⟩ := hcollision
  have htargetPrefix := hfirst htarget
  by_cases hfresh : prefixCache input = none
  · exact ⟨input, output, targetOutput, hfinal, hfresh, htargetPrefix, hdigest⟩
  · obtain ⟨prefixOutput, hprefix⟩ := Option.ne_none_iff_exists.mp hfresh
    have hprefix := hprefix.symm
    exfalso
    apply hnoPrefix
    refine ⟨input, prefixOutput, targetOutput, hprefix, hinitial, htarget, ?_⟩
    have hleft := (CacheView.digestAt_eq_of_cache_eq_some hprefix).trans
      (CacheView.digestAt_eq_of_cache_eq_some (hsecond hprefix)).symm
    have hright := (CacheView.digestAt_eq_of_cache_eq_some htargetPrefix).trans
      (CacheView.digestAt_eq_of_cache_eq_some (hsecond htargetPrefix)).symm
    exact hleft.trans (hdigest.trans hright.symm)

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
  apply adaptiveFreshCollision_split keygenCache prefixCache finalCache _ hkeygenLe hprefixLe
  · obtain ⟨input, output, targetOutput, hdeciding, hfinal, hkeygen, htarget, hdigest⟩ := hwitness
    have hmap := decidingTargetInput_eq_structural_of_isDecidingInput secretKey keygenCache
      leafIndex chain input hdeciding
    simp only [Rom.AdaptiveFreshDigestCollisionWith, OracleSpec.Range, HashSpec,
      RandomOracleModel.HashSpec, OracleSpec.ofFn]
    refine ⟨input, output, targetOutput, hfinal, hkeygen, ?_, ?_⟩
    · rw [hmap]
      exact htarget
    · rw [hmap]
      exact hdigest
  · intro hcollision
    exact hnoPrefix (adaptiveFreshDigestCollisionWith_structural_of_deciding
      keygenCache prefixCache secretKey keygenCache leafIndex chain hcollision)

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
  have hpred : (fun chain => decide (¬ChainTrivial cache secretKey log forgery forgedEnc chain)) =
      (fun chain => decide (¬ChainTrivial cache' secretKey log forgery forgedEnc chain)) := by
    funext chain
    simp only [htrivial]
  rw [hpred]

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
      simp only [hsig] at hentry
      cases hentry
  | some entrySignature =>
      simp only [hsig] at hentry
      by_cases hepoch : entry.1.epoch = leafIndex
      · rw [if_pos hepoch] at hentry
        cases hentry
        exact ⟨⟨entry, hmem, rfl, hsig⟩, hepoch⟩
      · rw [if_neg hepoch] at hentry
        cases hentry

end XmssSecurity.Generic.Deciding

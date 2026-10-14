import XmssSecurity.Proof.Direct.DecidingOrientation

/-!
# Deterministic classification on the deciding path

The structural alternative is restricted to one chain, the forged leaf, and its authentication
path. This restriction is what allows the verifier's contribution to be bounded by forty queries.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Deciding

open Concrete

theorem signedEncoding_valid (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (leafIndex : LeafIndex) (encoding : Encoding)
    (h : signedEncoding cache parameter log leafIndex = some encoding) :
    TargetSum.Valid encoding := by
  unfold signedEncoding at h
  split at h
  · cases h
  · exact (TargetSum.decodeDigest_eq_some_iff.mp h).2

/-- If every chain is trivial, the signed and forged encodings coincide. -/
theorem signedEncoding_eq_of_all_trivial (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (encoding : Encoding)
    (hvalid : TargetSum.Valid encoding)
    (htrivial : ∀ chain, ChainTrivial cache secretKey log forgery encoding chain) :
    signedEncoding cache secretKey.parameter log forgery.epoch = some encoding := by
  obtain ⟨signed, hsigned, _, _⟩ := htrivial ⟨0, by simp [numChains]⟩
  have heq : signed = encoding := TargetSum.eq_of_pointwiseLE_of_valid
    (signedEncoding_valid cache secretKey.parameter log forgery.epoch signed hsigned) hvalid
    (fun chain => by
      obtain ⟨signed', hsigned', hle, _⟩ := htrivial chain
      have : signed' = signed := Option.some.inj (hsigned'.symm.trans hsigned)
      simpa only [this] using hle)
  exact hsigned.trans (congrArg some heq)

/-- An honest value on a nontrivial deciding chain is necessarily hidden below the signed digit. -/
theorem deciding_revealed_of_honest (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (encoding : Encoding)
    (hdecode : forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some encoding)
    (hnot : ¬ ChainTrivial cache outcome.secretKey outcome.signingLog outcome.forgery encoding
      (decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding))
    (hhonest : outcome.forgery.signature.chainValue
        (decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding) =
      honestChainValue cache outcome.secretKey outcome.forgery.epoch
        (decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding)
        (encoding (decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery
          encoding))) :
    DecidingChainValueRevealed cache outcome := by
  refine ⟨encoding, hdecode, ?_, hhonest⟩
  intro signed hsigned
  exact lt_of_not_ge (fun hle => hnot ⟨signed, hsigned, hle, hhonest⟩)

/-- With an honest authentication path, all trivial chains force an encoding collision in a
strong forgery. -/
theorem encoding_event_of_all_trivial (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (hconsistent : ConcreteOutcomeConsistent cache outcome) (hwin : outcome.won = true)
    (encoding : Encoding)
    (hdecode : forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some encoding)
    (htrivial : ∀ chain, ChainTrivial cache outcome.secretKey outcome.signingLog
      outcome.forgery encoding chain)
    (hpath : outcome.forgery.signature.authPath =
      (CacheReplay.signWithEncoding cache outcome.secretKey outcome.forgery.epoch
        outcome.forgery.signature.randomness encoding).authPath) :
    OutcomeBadEventOccurs cache outcome .encoding := by
  have hsigned := signedEncoding_eq_of_all_trivial cache outcome.secretKey outcome.signingLog
    outcome.forgery encoding (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2 htrivial
  cases hreturned : returnedAt outcome.signingLog outcome.forgery.epoch with
  | none => simp [signedEncoding, hreturned] at hsigned
  | some pair =>
    rcases pair with ⟨request, signature⟩
    obtain ⟨hentry, hepoch⟩ := returned_of_returnedAt _ _ _ _ hreturned
    have hsignedDecode : TargetSum.decodeDigest
        (CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (request.message, signature.randomness)) = some encoding := by
      simpa only [signedEncoding, hreturned, hepoch] using hsigned
    obtain ⟨actual, hactual, hsignature⟩ := hconsistent.signing request signature hentry
    have hactualEq : actual = encoding := Option.some.inj (hactual.symm.trans hsignedDecode)
    subst actual
    have hinput : (request.message, signature.randomness) ≠
        (outcome.forgery.message, outcome.forgery.signature.randomness) := by
      intro heq
      have hvalue : signature.chainValue = outcome.forgery.signature.chainValue := by
        funext chain
        rw [hsignature]
        change honestChainValue cache outcome.secretKey request.epoch chain (encoding chain) = _
        rw [hepoch]
        obtain ⟨signed, hsigned', _, hvalue⟩ := htrivial chain
        have heq : signed = encoding := Option.some.inj (hsigned'.symm.trans hsigned)
        simpa only [heq] using hvalue.symm
      have hauth : signature.authPath = outcome.forgery.signature.authPath := by
        rw [hsignature, hepoch]
        exact hpath.symm
      have hsig : signature = outcome.forgery.signature := by
        cases signature
        cases hsig' : outcome.forgery.signature
        cases congrArg Prod.snd heq
        simp_all
      apply (outcome.won_eq_true_iff.mp hwin).2.1
      obtain ⟨entry, hmem, hrequest, hanswer⟩ := hentry
      refine ⟨entry, hmem, ?_, ?_⟩
      · rw [hrequest]
        exact congrArg₂ SUFCMA.SignRequest.mk hepoch (congrArg Prod.fst heq)
      · exact hanswer.trans (congrArg some hsig)
    have hforgedDecode : TargetSum.decodeDigest
        (CacheView.encodingHash cache outcome.secretKey.parameter request.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding := by
      simpa only [forgedEncoding, hepoch] using hdecode
    refine ⟨(outcome.won_eq_true_iff.mp hwin).2.2,
      Or.inl ⟨request, signature, encoding, encoding, hsignedDecode, hforgedDecode,
        hentry, hepoch, ?_⟩⟩
    exact TargetSum.hash_collision_of_same_decodedEncoding _ hinput hsignedDecode hforgedDecode

/-- A structural collision lying on the selected chain or above its leaf. -/
def DecidingStructuralCollision (cache : QueryCache HashSpec) (outcome : GameOutcome)
    (encoding : Encoding) : Prop :=
  let chain := decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding
  let step := fun c => CacheView.chainStep cache outcome.secretKey.parameter outcome.forgery.epoch c
  let endpoints := XmssSecurity.recoveredEndpoints step encoding outcome.forgery.signature.chainValue
  let honest := CacheReplay.oneTimePublicKey cache outcome.secretKey.parameter
    outcome.secretKey.chainStart outcome.forgery.epoch
  let leafHash := CacheView.leafHash cache outcome.secretKey.parameter outcome.forgery.epoch
  Wots.HasStepCollision (step chain) (encoding chain).val
      (chainLength - 1 - (encoding chain).val) (outcome.forgery.signature.chainValue chain)
      (honestChainValue cache outcome.secretKey outcome.forgery.epoch chain (encoding chain)) ∨
    Wots.HasLeafCollision leafHash endpoints honest ∨
    Merkle.HasXmssPathCollision
      (CacheView.nodeHash cache outcome.secretKey.parameter outcome.forgery.epoch)
      (signaturePath outcome.forgery.signature)
      (signaturePath (CacheReplay.signWithEncoding cache outcome.secretKey outcome.forgery.epoch
        outcome.forgery.signature.randomness encoding))
      (leafHash endpoints) (leafHash honest)

/-- Every consistent winning forgery has an encoding event, a hidden deciding value, or a
structural collision on the deciding path. -/
theorem winning_outcome_deciding_classification (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (hconsistent : ConcreteOutcomeConsistent cache outcome)
    (hwin : outcome.won = true) :
    OutcomeBadEventOccurs cache outcome .encoding ∨ DecidingChainValueRevealed cache outcome ∨
      ∃ encoding, forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some encoding ∧
        DecidingStructuralCollision cache outcome encoding := by
  have hverify : Concrete.verifyFromCache cache outcome.publicKey outcome.forgery.epoch
      outcome.forgery.message outcome.forgery.signature = true := by
    rw [← hconsistent.verification]
    exact (outcome.won_eq_true_iff.mp hwin).2.2
  rw [hconsistent.key] at hverify
  obtain ⟨encoding, hdecode, hroot⟩ := (Concrete.verifyFromCache_eq_true_iff cache _ _ _ _).mp hverify
  have hhonestRoot := CacheReplay.authenticationPath_ascends_to_root cache outcome.secretKey
    outcome.forgery.epoch outcome.forgery.signature.randomness encoding
  simp only [CacheReplay.publicKeyFromCache] at hdecode hroot
  have hroots := hroot.trans hhonestRoot.symm
  rcases Merkle.sameXmssPath_or_hasCollision _ _ _ _ _ hroots with ⟨hleaf, hpath⟩ | hmerkle
  · rcases Wots.eq_or_hasLeafCollision _ _ _ hleaf with hendpoints | hleafCollision
    · rcases decidingChain_trivial_or_not cache outcome.secretKey outcome.signingLog
        outcome.forgery encoding with htrivial | hnontrivial
      · exact Or.inl (encoding_event_of_all_trivial cache outcome hconsistent hwin encoding
          hdecode htrivial (Concrete.same_signaturePath_iff.mp hpath))
      · let chain := decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery encoding
        have hend := congrFun hendpoints chain
        change Wots.recoverChain
            (CacheView.chainStep cache outcome.secretKey.parameter outcome.forgery.epoch chain)
            (encoding chain) (outcome.forgery.signature.chainValue chain) =
          Wots.publicChain
            (CacheView.chainStep cache outcome.secretKey.parameter outcome.forgery.epoch chain)
            (outcome.secretKey.chainStart outcome.forgery.epoch chain) at hend
        rw [← Wots.recover_signChain_eq_publicChain
          (CacheView.chainStep cache outcome.secretKey.parameter outcome.forgery.epoch chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain)] at hend
        rcases Wots.eq_or_hasStepCollision _ _ _ _ _ hend with hvalue | hcollision
        · exact Or.inr (Or.inl (deciding_revealed_of_honest cache outcome encoding hdecode
            hnontrivial hvalue))
        · exact Or.inr (Or.inr ⟨encoding, hdecode, Or.inl hcollision⟩)
    · exact Or.inr (Or.inr ⟨encoding, hdecode, Or.inr (Or.inl hleafCollision)⟩)
  · exact Or.inr (Or.inr ⟨encoding, hdecode, Or.inr (Or.inr hmerkle)⟩)

end XmssSecurity.Deciding

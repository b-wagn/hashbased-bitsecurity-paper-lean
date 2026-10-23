import Xmss.Proof.Generic.IdealStatement
import Xmss.Proof.Generic.StatementLemmas
import Xmss.Proof.Generic.ForgeryCases

open OracleSpec

namespace Xmss.Generic

open Hashing Wots Merkle Verify Keygen Signing

variable [Code]

theorem Verify.same_signaturePath_iff {left right : Signature} :
    Merkle.SamePathSegment (signaturePath left) (signaturePath right) 0 treeHeight ↔
      left.authPath = right.authPath := by
  constructor
  · intro hpath
    funext level
    have heq := hpath level.val level.isLt
    simpa [signaturePath] using heq
  · intro hpath level hlevel
    simp [signaturePath, hlevel, hpath]

theorem Verify.strong_components {signedMessage forgedMessage : Message}
    {signedSignature forgedSignature : Signature}
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature) :
    (signedMessage, signedSignature.randomness) ≠
        (forgedMessage, forgedSignature.randomness) ∨
      signedSignature.chainValue ≠ forgedSignature.chainValue ∨
      ¬Merkle.SamePathSegment (signaturePath signedSignature)
        (signaturePath forgedSignature) 0 treeHeight := by
  by_cases hinput :
      (signedMessage, signedSignature.randomness) =
        (forgedMessage, forgedSignature.randomness)
  · by_cases hvalues : signedSignature.chainValue = forgedSignature.chainValue
    · right
      right
      intro hpath
      apply hstrong.elim
      · intro hmessage
        exact hmessage (congrArg Prod.fst hinput)
      · intro hsignature
        apply hsignature
        have hauth := same_signaturePath_iff.mp hpath
        cases signedSignature
        cases forgedSignature
        simp_all
    · exact Or.inr (Or.inl hvalues)
  · exact Or.inl hinput

noncomputable def Verify.SameLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedValid : Code.Valid signedEncoding) : BadEvent → Prop :=
  Xmss.Generic.SameLeafIndexBadEventOccurs
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    hsignedValid

/-- Concrete same-leaf-index strong forgeries select one of the 175 cache-level bad events. -/
theorem Verify.sameLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signedMessage forgedMessage : Message)
    (signedEncoding forgedEncoding : Encoding)
    (signedSignature forgedSignature : Signature)
    (hsignedEncoding : CacheView.decodedEncoding cache parameter leafIndex
        (signedMessage, signedSignature.randomness) = some signedEncoding)
    (hforgedEncoding : CacheView.decodedEncoding cache parameter leafIndex
        (forgedMessage, forgedSignature.randomness) = some forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath signedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            signedEncoding signedSignature.chainValue)))
    (hstrong : signedMessage ≠ forgedMessage ∨ signedSignature ≠ forgedSignature) :
    ∃ event, SameLeafIndexBadEventOccurs cache parameter leafIndex
      signedMessage forgedMessage signedEncoding forgedEncoding
      signedSignature forgedSignature
      (CacheView.decodedEncoding_valid hsignedEncoding) event := by
  exact Xmss.Generic.sameLeafIndex_forgery_has_badEvent
    (CacheView.encodingHash cache parameter leafIndex)
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    (signedMessage, signedSignature.randomness)
    (forgedMessage, forgedSignature.randomness)
    signedEncoding forgedEncoding
    signedSignature.chainValue forgedSignature.chainValue
    (signaturePath signedSignature) (signaturePath forgedSignature)
    (CacheView.decodeDigest_of_decodedEncoding hsignedEncoding)
    (CacheView.decodeDigest_of_decodedEncoding hforgedEncoding) hroot (strong_components hstrong)

noncomputable def Verify.FreshLeafIndexBadEventOccurs
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : Code.Valid forgedEncoding) : BadEvent → Prop :=
  Xmss.Generic.FreshLeafIndexBadEventOccurs
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid

/-- Concrete fresh-leaf-index forgeries select one of the same 175 cache-level bad events. -/
theorem Verify.freshLeafIndex_forgery_has_badEvent
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (forgedEncoding : Encoding) (forgedSignature : Signature)
    (secret : ChainIndex → Digest) (honestPath : Nat → Digest)
    (hforgedValid : Code.Valid forgedEncoding)
    (hroot : Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (signaturePath forgedSignature) 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (recoveredEndpoints
            (fun chain => CacheView.chainStep cache parameter leafIndex chain)
            forgedEncoding forgedSignature.chainValue)) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        honestPath 0 treeHeight
        (CacheView.leafHash cache parameter leafIndex
          (fun chain => Wots.publicChain
            (CacheView.chainStep cache parameter leafIndex chain) (secret chain)))) :
    ∃ event, FreshLeafIndexBadEventOccurs cache parameter leafIndex forgedEncoding
      forgedSignature secret honestPath hforgedValid event := by
  exact Xmss.Generic.freshLeafIndex_forgery_has_badEvent
    (fun chain => CacheView.chainStep cache parameter leafIndex chain)
    (CacheView.leafHash cache parameter leafIndex)
    (CacheView.nodeHash cache parameter leafIndex)
    forgedEncoding forgedSignature.chainValue secret
    (signaturePath forgedSignature) honestPath hforgedValid hroot

end Xmss.Generic

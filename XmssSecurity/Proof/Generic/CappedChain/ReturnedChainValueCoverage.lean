import XmssSecurity.Proof.Generic.CappedChain.ChainRevealFiltering

open OracleComp OracleSpec

namespace XmssSecurity.Generic.CappedChain

variable [Code]

def ChainValueIndicesForwardClosed
    (covered : Set ChainValueIndex) : Prop :=
  ∀ leafIndex earlier later,
    (leafIndex, earlier) ∈ covered → earlier ≤ later →
      (leafIndex, later) ∈ covered

noncomputable def ReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    Set ChainValueIndex :=
  fun index => index ∈ returnedChainValueIndexList cache secretKey log chain

theorem returnedChainValueCovered_iff
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (index : ChainValueIndex) :
    index ∈ ReturnedChainValueCovered cache secretKey log chain ↔
      ∃ request signature encoding,
        SigningTranscript.Returned log request signature ∧
          Concrete.CacheView.decodedEncoding cache secretKey.parameter
              request.epoch
              (request.message, signature.randomness) = some encoding ∧
          index.1 = request.epoch ∧ encoding chain ≤ index.2 := by
  exact mem_returnedChainValueIndexList_iff cache secretKey log chain index

theorem returnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex) :
    ChainValueIndicesForwardClosed
      (ReturnedChainValueCovered cache secretKey log chain) := by
  intro leafIndex earlier later hmem hle
  rw [returnedChainValueCovered_iff] at hmem ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode,
    hleafIndex, hdigit⟩ := hmem
  exact ⟨request, signature, encoding, hreturned, hdecode,
    hleafIndex, hdigit.trans hle⟩

theorem returnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (chain : ChainIndex)
    (request : SignRequest) (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : Concrete.CacheView.decodedEncoding cache secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding) :
    (request.epoch, encoding chain) ∈
      ReturnedChainValueCovered cache secretKey log chain := by
  rw [returnedChainValueCovered_iff]
  exact ⟨request, signature, encoding, hreturned, hdecode, rfl, le_rfl⟩

end XmssSecurity.Generic.CappedChain

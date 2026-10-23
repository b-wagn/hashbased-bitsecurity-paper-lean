import Xmss.Proof.Generic.PrecomputedKeygenCache
import Xmss.Proof.Generic.ChainOraclePresampling
import Xmss.Proof.Generic.CappedExecution.ChainHiddenTable

open OracleComp OracleSpec

namespace Xmss.Generic.CappedExecution

variable [Code]

def replaceSignatureChainValue
    (signature : Signature) (chain : ChainIndex) (value : Digest) : Signature :=
  { signature with
    chainValue := Function.update signature.chainValue chain value }

@[simp]
theorem replaceSignatureChainValue_same
    (signature : Signature) (chain : ChainIndex) (value : Digest) :
    (replaceSignatureChainValue signature chain value).chainValue chain = value := by
  simp [replaceSignatureChainValue]

theorem replaceSignatureChainValue_other
    (signature : Signature) (chain candidate : ChainIndex) (value : Digest)
    (hne : candidate ≠ chain) :
    (replaceSignatureChainValue signature chain value).chainValue candidate =
      signature.chainValue candidate := by
  simp [replaceSignatureChainValue, Function.update_of_ne hne]

theorem CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding)
    (chain : ChainIndex) :
    (CacheReplay.signWithEncoding largerCache keyResult.1.2
      leafIndex randomness encoding).chainValue chain =
      keygenChainValueTable keyResult.2 keyResult.1.2 chain
        (leafIndex, encoding chain) := by
  have hwalk := Keygen.keygen_chainWalk_eq_of_cache_le keyResult hkeygen
    largerCache hle leafIndex chain (encoding chain).val
    (Nat.le_pred_of_lt (encoding chain).isLt)
  simp only [CacheReplay.signWithEncoding,
    CacheReplay.signedChainValues, keygenChainValueTable]
  exact hwalk.symm

end Xmss.Generic.CappedExecution

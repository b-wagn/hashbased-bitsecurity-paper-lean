import XmssSecurity.Proof.TargetSum.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget

/-! A fresh verification encoding is accepted with its ordinary sampling probability.
The same bound applies when the entire prefix cache contains no accepted encoding. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

theorem verifyAfterDigest_eq_false_of_invalid (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (digest : Digest) (hinvalid : ¬TargetSum.ValidDigest digest) :
    verifyAfterDigest publicKey leafIndex signature digest = pure false := by
  unfold verifyAfterDigest
  cases hdecode : TargetSum.decodeDigest digest with
  | none => rfl
  | some encoding => exact (hinvalid ⟨encoding, hdecode⟩).elim

theorem verify_run_fresh (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    (simulateQ romImpl (Concrete.scheme.verify publicKey leafIndex message signature)).run cache = (do
      let output ← ($ᵗ HashOutput)
      (simulateQ randomOracle (verifyAfterDigest publicKey leafIndex signature (truncateHash output))).run
        (cache.cacheQuery (Concrete.CacheView.encodingInput publicKey.parameter leafIndex
          (message, signature.randomness)) output)) := by
  rw [simulateQ_romImpl_scheme_verify, StateT.run_bind,
    randomOracle_run_none_eq_uniformHashOutput _ _ hfresh, bind_map_left]
  rfl

end XmssSecurity.TargetSum.Direct

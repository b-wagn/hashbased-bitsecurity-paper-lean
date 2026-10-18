import XmssSecurity.Proof.Generic.Direct.ForgedEncodingQuery
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A fresh verification encoding is accepted with its ordinary sampling probability.
The same bound applies when the entire prefix cache contains no accepted encoding. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

theorem verifyAfterDigest_eq_false_of_invalid (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (digest : Digest) (hinvalid : ¬Generic.Code.ValidDigest digest) :
    Generic.Direct.verifyAfterDigest publicKey leafIndex signature digest = pure false := by
  unfold Generic.Direct.verifyAfterDigest
  cases hdecode : Generic.Code.decodeDigest digest with
  | none => rfl
  | some encoding => exact (hinvalid ⟨encoding, hdecode⟩).elim

theorem verify_run_fresh (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Generic.Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (Generic.Concrete.CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    (simulateQ Generic.romImpl (Generic.Concrete.scheme.verify publicKey leafIndex message signature)).run cache = (do
      let output ← ($ᵗ HashOutput)
      (simulateQ randomOracle (Generic.Direct.verifyAfterDigest publicKey leafIndex signature (Generic.truncateHash output))).run
        (cache.cacheQuery (Generic.Concrete.CacheView.encodingInput publicKey.parameter leafIndex
          (message, signature.randomness)) output)) := by
  rw [Generic.Direct.simulateQ_romImpl_scheme_verify, StateT.run_bind,
    Generic.randomOracle_run_none_eq_uniformHashOutput _ _ hfresh, bind_map_left]
  rfl

end XmssSecurity.TargetSum.Direct

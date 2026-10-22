import Xmss.Proof.Generic.Direct.ForgedEncodingQuery
import Xmss.Proof.TargetSum.EncodingAcceptanceBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A fresh verification encoding is accepted with its ordinary sampling probability.
The same bound applies when the entire prefix cache contains no accepted encoding. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Direct

theorem verifyAfterDigest_eq_false_of_invalid (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (digest : Digest) (hinvalid : ¬Code.ValidDigest digest) :
    Direct.verifyAfterDigest publicKey leafIndex signature digest = pure false := by
  unfold Direct.verifyAfterDigest
  cases hdecode : Code.decodeDigest digest with
  | none => rfl
  | some encoding => exact (hinvalid ⟨encoding, hdecode⟩).elim

theorem verify_run_fresh (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Generic.Signature) (cache : QueryCache HashSpec)
    (hfresh : cache (CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = none) :
    (simulateQ romImpl (precomputedScheme.verify publicKey leafIndex message signature)).run cache = (do
      let output ← ($ᵗ Digest)
      (simulateQ randomOracle (Direct.verifyAfterDigest publicKey leafIndex signature (output))).run
        (cache.cacheQuery (CacheView.encodingInput publicKey.parameter leafIndex
          (message, signature.randomness)) output)) := by
  rw [Direct.simulateQ_romImpl_scheme_verify, StateT.run_bind,
    randomOracle_run_none_eq_uniformHashOutput _ _ hfresh, bind_map_left]
  rfl

end Xmss.TargetSum.Direct

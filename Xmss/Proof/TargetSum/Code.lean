import Xmss.Proof.Generic.Code
import Xmss.Proof.TargetSum.EncodingLemmas

/-! The target-sum code as an instance of `Code`, scoped to `Xmss.TargetSum`. -/

open Xmss.Generic

namespace Xmss.TargetSum

scoped instance code : Code where
  numChains := numChains
  numChains_pos := by decide
  numChains_lt := by decide
  decodeDigest := TargetSum.decodeDigest
  Valid := TargetSum.Valid
  validDecidable := inferInstance
  signingAttemptLimit := signingAttemptLimit
  signingAttemptLimit_pos := by decide
  signingAttemptLimit_le := by decide
  verificationChainHashes := verificationChainHashes
  decodeDigest_valid h := (TargetSum.decodeDigest_eq_some_iff.mp h).2
  digest_eq_of_decodeDigest_eq_some := TargetSum.digest_eq_of_decodeDigest_eq_some
  eq_of_pointwiseLE_of_valid hx hy h := TargetSum.eq_of_pointwiseLE_of_valid hx hy h
  verificationWork_le hx := (TargetSum.verificationWork_eq _ hx).le
  exists_decodes := TargetSum.exists_decodes

@[simp] theorem code_signingAttemptLimit :
    Code.signingAttemptLimit = signingAttemptLimit := rfl

@[simp] theorem code_numChains : Code.numChains = numChains := rfl

end Xmss.TargetSum

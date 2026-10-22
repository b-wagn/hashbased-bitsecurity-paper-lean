import Xmss.Proof.Generic.Code
import Xmss.Proof.Checksum.EncodingLemmas

/-! The checksummed code as an instance of `Code`, scoped to `Xmss.Checksum`. -/

open Xmss.Generic

namespace Xmss.Checksum

scoped instance code : Code where
  numChains := numChains
  numChains_pos := by decide
  numChains_lt := by decide
  decodeDigest := Checksum.decodeDigest
  Valid := Checksum.Valid
  validDecidable := inferInstance
  signingAttemptLimit := signingAttemptLimit
  signingAttemptLimit_pos := by decide
  signingAttemptLimit_le := by decide
  verificationChainHashes := verificationChainHashes
  decodeDigest_valid := Checksum.decodeDigest_valid
  digest_eq_of_decodeDigest_eq_some := Checksum.digest_eq_of_decodeDigest_eq_some
  eq_of_pointwiseLE_of_valid hx hy h := Checksum.eq_of_pointwiseLE_of_valid hx hy h
  verificationWork_le _ := Checksum.verificationWork_le _
  exists_decodes := ⟨0, encode 0, rfl⟩

@[simp] theorem code_signingAttemptLimit :
    Code.signingAttemptLimit = signingAttemptLimit := rfl

@[simp] theorem code_numChains : Code.numChains = numChains := rfl

end Xmss.Checksum

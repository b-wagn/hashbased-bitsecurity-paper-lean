import XmssSecurity.Proof.Modes.Keygen
import XmssSecurity.Proof.Modes.Projection

/-!
# Security when the signer's hash calls are charged

TODO (work in progress): `123` bits when the signer is charged, and `124` bits when the signer and
the signing requests are charged.
-/

namespace XmssSecurity.Modes

theorem sufCmaSigner_123 :
    (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 123 := by
  sorry

theorem sufCmaSignerRequests_124 :
    (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss 124 := by
  sorry

end XmssSecurity.Modes

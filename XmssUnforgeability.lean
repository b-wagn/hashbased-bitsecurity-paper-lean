import XmssSecurity
import XmssSecurity.Statement.EUFCMAClaims
import XmssSecurity.Proof.EUFCMA.Reduction

/-! Standard (non-strong) unforgeability of the unchanged XMSS scheme.
Freshness concerns the requested epoch/message pair. The completed strong-security
development supplies initial lower bounds; the direct 127-bit bound and the
standard-forgery upper bounds are separate proof obligations. -/

namespace XmssSecurity

open SUFCMA

/-- Every counting mode inherits at least 122 bits of standard security. -/
theorem xmss_eufCma_secure_122 (mode : CountingMode) : XmssEufCmaSecure mode 122 :=
  EUFCMA.security_of_strong mode xmss 122 (xmss_sufCma_secure_122 mode)

/-- info: 'XmssSecurity.xmss_eufCma_secure_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_secure_122

/-- The fourteen modes charging any honest-party hashes inherit 127 bits. -/
theorem xmss_eufCma_secure_127_of_honest_hashes (mode : CountingMode)
    (hcharged : mode.keygen = true ∨ mode.signer = true ∨ mode.verifier = true) :
    XmssEufCmaSecure mode 127 :=
  EUFCMA.security_of_strong mode xmss 127
    (Modes.secure_127_of_minimal_modes xmss_sufCma_keygen_127 xmss_sufCma_signer_127
      xmss_sufCma_verifier_127 mode (by simpa only [Bool.or_eq_true, or_assoc] using hcharged))

/-- info: 'XmssSecurity.xmss_eufCma_secure_127_of_honest_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_secure_127_of_honest_hashes

end XmssSecurity

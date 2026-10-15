import XmssSecurity
import XmssSecurity.Statement.EUFCMAClaims
import XmssSecurity.Proof.EUFCMA.Reduction
import XmssSecurity.Proof.EUFCMA.NeighborAttack
import XmssSecurity.Proof.EUFCMA.Exact

/-! Standard (non-strong) unforgeability of the unchanged XMSS scheme.
Freshness concerns the requested epoch/message pair. The completed strong-security
development supplies initial lower bounds. The neighboring-message attack proves
the upper bound in every mode; the direct 127-bit lower bound remains open. -/

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

/-- The neighboring-message forgery refutes 128 bits even with everything charged. -/
theorem xmss_eufCma_everything_attack_127 : XmssEufCmaEverythingAttackStatement :=
  Attack.neighbor_euf_everything_attack

/-- info: 'XmssSecurity.xmss_eufCma_everything_attack_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_everything_attack_127

/-- Every counting mode inherits the standard-forgery attack against 128 bits. -/
theorem xmss_eufCma_attack_127 (mode : CountingMode) : XmssEufCmaAttack mode 127 :=
  EUFCMA.not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128
    xmss_eufCma_everything_attack_127

/-- info: 'XmssSecurity.xmss_eufCma_attack_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_attack_127

/-- Fourteen counting modes have exactly 127 bits of standard unforgeability. -/
theorem xmss_eufCma_exact_127_of_honest_hashes (mode : CountingMode)
    (hcharged : mode.keygen = true ∨ mode.signer = true ∨ mode.verifier = true) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127 :=
  ⟨xmss_eufCma_secure_127_of_honest_hashes mode hcharged, xmss_eufCma_attack_127 mode⟩

/-- info: 'XmssSecurity.xmss_eufCma_exact_127_of_honest_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact_127_of_honest_hashes

/-- The only remaining basis obligation is the direct-query 127-bit lower bound. -/
theorem xmss_eufCma_exact_iff_direct_127 :
    XmssEufCmaExactStatement ↔ XmssEufCmaDirectStatement := by
  rw [EUFCMA.exactStatement_iff_basis]
  exact ⟨And.left, fun hd => ⟨hd, xmss_eufCma_everything_attack_127⟩⟩

/-- info: 'XmssSecurity.xmss_eufCma_exact_iff_direct_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact_iff_direct_127

end XmssSecurity

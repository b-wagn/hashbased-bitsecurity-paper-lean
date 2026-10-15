import XmssSecurity
import XmssSecurity.Statement.EUFCMAClaims
import XmssSecurity.Proof.EUFCMA.Reduction
import XmssSecurity.Proof.EUFCMA.NeighborAttack
import XmssSecurity.Proof.EUFCMA.Exact
import XmssSecurity.Proof.EUFCMA.DirectBridge
import XmssSecurity.Proof.EUFCMA.FreshAcceptancePrefix
import XmssSecurity.Proof.EUFCMA.ReferenceHop
import XmssSecurity.Proof.EUFCMA.DirectSecurity
import XmssSecurity.Proof.EUFCMA.ReplayFallback
import XmssSecurity.Proof.EUFCMA.ReplayAccounting
import XmssSecurity.Proof.EUFCMA.Direct126
import XmssSecurity.Proof.EUFCMA.RequestsBridge
import XmssSecurity.Proof.EUFCMA.RequestsExpected
import XmssSecurity.Proof.EUFCMA.RequestsActivity
import XmssSecurity.Proof.EUFCMA.RequestsTerminalFirstLane
import XmssSecurity.Proof.EUFCMA.RequestsEncodingCollision
import XmssSecurity.Proof.EUFCMA.ExpectedSecondLane
import XmssSecurity.Proof.EUFCMA.ExpectedDirectSeed

/-! Standard (non-strong) unforgeability of the unchanged XMSS scheme.
Freshness concerns the requested epoch/message pair. The completed strong-security
development supplies initial lower bounds. The neighboring-message attack proves
the upper bound in every mode. A fresh-message replay/fallback attack refutes
127-bit direct-only security, and the matching lower bound establishes exactly
126 bits in that mode. Only the direct-plus-signing-requests mode remains open. -/

namespace XmssSecurity

open SUFCMA

/-- Every counting mode inherits at least 122 bits of standard security. -/
theorem xmss_eufCma_secure_122 (mode : CountingMode) : XmssEufCmaSecure mode 122 :=
  EUFCMA.security_of_strong mode xmss 122 (xmss_sufCma_secure_122 mode)

/-- info: 'XmssSecurity.xmss_eufCma_secure_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_secure_122

/-- Standard freshness improves direct-query security to at least 125 bits. -/
theorem xmss_eufCma_direct_125 : XmssEufCmaSecure CountingMode.direct 125 :=
  EUFCMA.direct_125

/-- info: 'XmssSecurity.xmss_eufCma_direct_125' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_direct_125

/-- Every counting mode has at least 125 bits of standard security. -/
theorem xmss_eufCma_secure_125 (mode : CountingMode) : XmssEufCmaSecure mode 125 :=
  EUFCMA.hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 125 xmss_eufCma_direct_125

/-- info: 'XmssSecurity.xmss_eufCma_secure_125' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_secure_125

/-- The fresh terminal-probe estimate gives exactly 126 direct-query bits. -/
theorem xmss_eufCma_direct_exact_126 :
    (EUFCMA.notion CountingMode.direct).HasExactClassicalSecurityBits xmss 126 :=
  EUFCMA.direct_exact_126

/-- info: 'XmssSecurity.xmss_eufCma_direct_exact_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_direct_exact_126

/-- Every counting mode has at least 126 bits of standard security. -/
theorem xmss_eufCma_secure_126 (mode : CountingMode) : XmssEufCmaSecure mode 126 :=
  EUFCMA.hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 126 EUFCMA.direct_126

/-- info: 'XmssSecurity.xmss_eufCma_secure_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_secure_126

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

/-- A one-query standard forgery refutes 127 bits in the direct-only mode. -/
theorem xmss_eufCma_direct_attack_126 : XmssEufCmaAttack CountingMode.direct 126 :=
  EUFCMA.replay_direct_attack_126

/-- info: 'XmssSecurity.xmss_eufCma_direct_attack_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_direct_attack_126

/-- The initial uniform 127-bit conjecture is false. -/
theorem xmss_eufCma_not_uniform_127 : ¬XmssEufCmaExactStatement :=
  EUFCMA.not_uniform_127

/-- info: 'XmssSecurity.xmss_eufCma_not_uniform_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_not_uniform_127

/-- Fourteen counting modes have exactly 127 bits of standard unforgeability. -/
theorem xmss_eufCma_exact_127_of_honest_hashes (mode : CountingMode)
    (hcharged : mode.keygen = true ∨ mode.signer = true ∨ mode.verifier = true) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127 :=
  ⟨xmss_eufCma_secure_127_of_honest_hashes mode hcharged, xmss_eufCma_attack_127 mode⟩

/-- info: 'XmssSecurity.xmss_eufCma_exact_127_of_honest_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact_127_of_honest_hashes

/-- The initial all-127 conjecture is equivalent to its direct-query target.
Both sides have now been refuted by the replay/fallback attack. -/
theorem xmss_eufCma_exact_iff_direct_127 :
    XmssEufCmaExactStatement ↔ XmssEufCmaDirectStatement := by
  rw [EUFCMA.exactStatement_iff_basis]
  exact ⟨And.left, fun hd => ⟨hd, xmss_eufCma_everything_attack_127⟩⟩

/-- info: 'XmssSecurity.xmss_eufCma_exact_iff_direct_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_eufCma_exact_iff_direct_127

end XmssSecurity

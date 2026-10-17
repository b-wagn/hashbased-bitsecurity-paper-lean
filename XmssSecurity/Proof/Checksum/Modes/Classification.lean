import XmssSecurity.Proof.Checksum.Modes.Exact
import XmssSecurity.Proof.Common.EUFCMA.Modes
import XmssSecurity.Proof.Common.EUFCMA.Reduction

/-!
# A basis for the exact classification

The exact bit security of a counting mode is `127` if it charges key generation or verification,
and otherwise `124` if it charges the signer and the signing requests, `123` if it charges the
signer only, and `122` if it charges neither. Five security proofs in the minimal modes of the four
levels and four attacks in their maximal modes cover all sixteen modes, by monotonicity in the mode
(`Lattice.lean`). Standard unforgeability inherits the five security proofs from strong
unforgeability.
-/

namespace XmssSecurity.Checksum.Modes
open XmssSecurity.Modes

open SUFCMA

/-- The exact bit security of a counting mode. -/
def exactLevel (mode : CountingMode) : ℕ :=
  if mode.keygen || mode.verifier then 127
  else if mode.signer && mode.requests then 124
  else if mode.signer then 123
  else 122

/-- The strong classification from five security proofs and four attacks. -/
theorem exactStatement_of_checksumBasis
    (hd : (SUFCMA.notion CountingMode.direct).HasClassicalSecurityBits xmss 122)
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 123)
    (hsr : (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss 124)
    (ha122 : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1))
    (ha123 : ¬(SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss (123 + 1))
    (ha124 : ¬(SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss (124 + 1))
    (ha127 : ¬(SUFCMA.notion CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1))
    (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss (exactLevel mode) := by
  rcases mode with ⟨keygen, signer, verifier, requests⟩
  cases keygen <;> cases verifier
  · -- Neither key generation nor verification.
    cases signer <;> cases requests
    · exact ⟨hd, not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le]) xmss 123 ha122⟩
    · exact ⟨hasClassicalSecurityBits_of_le (direct_le _) xmss 122 hd, ha122⟩
    · exact ⟨hs, ha123⟩
    · exact ⟨hsr, ha124⟩
  all_goals
    refine ⟨?_, not_hasClassicalSecurityBits_of_le (le_everything _) xmss 128 ha127⟩
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hv
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hk

/-- The standard classification from the strong security proofs and four standard attacks. -/
theorem eufExactStatement_of_checksumBasis
    (hd : (SUFCMA.notion CountingMode.direct).HasClassicalSecurityBits xmss 122)
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 123)
    (hsr : (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss 124)
    (ha122 : ¬(EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1))
    (ha123 : ¬(EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss (123 + 1))
    (ha124 : ¬(EUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss (124 + 1))
    (ha127 : ¬(EUFCMA.notion CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1))
    (mode : CountingMode) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss (exactLevel mode) := by
  have hd' := EUFCMA.security_of_strong _ xmss 122 hd
  have hk' := EUFCMA.security_of_strong _ xmss 127 hk
  have hv' := EUFCMA.security_of_strong _ xmss 127 hv
  have hs' := EUFCMA.security_of_strong _ xmss 123 hs
  have hsr' := EUFCMA.security_of_strong _ xmss 124 hsr
  rcases mode with ⟨keygen, signer, verifier, requests⟩
  cases keygen <;> cases verifier
  · cases signer <;> cases requests
    · exact ⟨hd', EUFCMA.not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le]) xmss 123 ha122⟩
    · exact ⟨EUFCMA.hasClassicalSecurityBits_of_le (direct_le _) xmss 122 hd', ha122⟩
    · exact ⟨hs', ha123⟩
    · exact ⟨hsr', ha124⟩
  all_goals
    refine ⟨?_, EUFCMA.not_hasClassicalSecurityBits_of_le (le_everything _) xmss 128 ha127⟩
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hv'
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hk'
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) xmss 127 hk'

end XmssSecurity.Checksum.Modes

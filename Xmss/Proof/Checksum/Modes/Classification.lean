import Xmss.Proof.Generic.Modes.Exact
import Xmss.Proof.Common.EUFCMA.Modes
import Xmss.Proof.Common.EUFCMA.Reduction
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-!
# A basis for the exact classification

All modes have exact integer levels: 127 when key generation or verification is charged,
124 when signer hashes and requests are charged, 123 for signer hashes alone, and 122 otherwise.
Standard unforgeability inherits the security proofs from strong unforgeability.
-/

open Xmss.Generic

namespace Xmss.Checksum.Modes
open Xmss.Modes

open Unforgeability SUFCMA

/-- The exact bit security of a counting mode. -/
def exactLevel (mode : CountingMode) : ℕ :=
  if mode.keygen || mode.verifier then 127
  else if mode.signer then (if mode.requests then 124 else 123)
  else 122

/-- The strong classification from five security proofs and four attacks. -/
theorem exactStatement_of_checksumBasis
    (hd : (SUFCMA.notion CountingMode.direct).HasClassicalSecurityBits Generic.xmss 122)
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss 123)
    (hsr : (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss 124)
    (ha122 : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss (122 + 1))
    (ha123 : ¬(SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss (123 + 1))
    (ha124 : ¬(SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss (124 + 1))
    (ha127 : ¬(SUFCMA.notion CountingMode.everything).HasClassicalSecurityBits Generic.xmss (127 + 1))
    (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss (exactLevel mode) := by
  rcases mode with ⟨keygen, signer, verifier, requests⟩
  cases keygen <;> cases verifier
  · -- Neither key generation nor verification.
    cases signer <;> cases requests
    · exact ⟨hd, not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le]) Generic.xmss 123 ha122⟩
    · exact ⟨hasClassicalSecurityBits_of_le (Modes.direct_le _) Generic.xmss 122 hd, ha122⟩
    · exact ⟨hs, ha123⟩
    · exact ⟨hsr, ha124⟩
  all_goals
    refine ⟨?_, not_hasClassicalSecurityBits_of_le (Modes.le_everything _) Generic.xmss 128 ha127⟩
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hv
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hk

/-- The standard classification from the strong security proofs and four standard attacks. -/
theorem eufExactStatement_of_checksumBasis
    (hd : (SUFCMA.notion CountingMode.direct).HasClassicalSecurityBits Generic.xmss 122)
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss 123)
    (hsr : (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss 124)
    (ha122 : ¬(EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss (122 + 1))
    (ha123 : ¬(EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss (123 + 1))
    (ha124 : ¬(EUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss (124 + 1))
    (ha127 : ¬(EUFCMA.notion CountingMode.everything).HasClassicalSecurityBits Generic.xmss (127 + 1))
    (mode : CountingMode) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss (exactLevel mode) := by
  have hd' := EUFCMA.security_of_strong _ Generic.xmss 122 hd
  have hk' := EUFCMA.security_of_strong _ Generic.xmss 127 hk
  have hv' := EUFCMA.security_of_strong _ Generic.xmss 127 hv
  have hs' := EUFCMA.security_of_strong _ Generic.xmss 123 hs
  have hsr' := EUFCMA.security_of_strong _ Generic.xmss 124 hsr
  rcases mode with ⟨keygen, signer, verifier, requests⟩
  cases keygen <;> cases verifier
  · cases signer <;> cases requests
    · exact ⟨hd', EUFCMA.not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le]) Generic.xmss 123 ha122⟩
    · exact ⟨EUFCMA.hasClassicalSecurityBits_of_le (Modes.direct_le _) Generic.xmss 122 hd', ha122⟩
    · exact ⟨hs', ha123⟩
    · exact ⟨hsr', ha124⟩
  all_goals
    refine ⟨?_, EUFCMA.not_hasClassicalSecurityBits_of_le (Modes.le_everything _) Generic.xmss 128 ha127⟩
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hv'
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hk'
  · exact EUFCMA.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le]) Generic.xmss 127 hk'

end Xmss.Checksum.Modes

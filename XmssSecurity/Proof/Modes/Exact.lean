import XmssSecurity.Statement.Claims
import XmssSecurity.Proof.Modes.Lattice

/-!
# A basis for the exact-security conjecture

Four lower bounds and two attacks suffice for all sixteen modes. In particular, the 122-bit
attack must allow charging signing requests: an attack proved only for `direct` does not by itself
give the upper bound for that larger mode.
-/

namespace XmssSecurity.Modes

open SUFCMA

theorem direct_le (mode : CountingMode) : CountingMode.direct.Le mode := by
  simp [CountingMode.Le, CountingMode.direct]

theorem le_everything (mode : CountingMode) : mode.Le CountingMode.everything := by
  simp [CountingMode.Le, CountingMode.everything]

/-- The three minimal modes charging an honest party cover every such counting mode. -/
theorem secure_127_of_minimal_modes
    (hk : XmssSufCmaSecure ⟨true, false, false, false⟩ 127)
    (hs : XmssSufCmaSecure ⟨false, true, false, false⟩ 127)
    (hv : XmssSufCmaSecure ⟨false, false, true, false⟩ 127)
    (mode : CountingMode) (h : (mode.keygen || mode.signer || mode.verifier) = true) :
    XmssSufCmaSecure mode 127 := by
  simp only [Bool.or_eq_true] at h
  rcases h with (hkeygen | hsigner) | hverifier
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hkeygen]) xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hsigner]) xmss 127 hs
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hverifier]) xmss 127 hv

/-- Assemble the exact-security picture from the four minimal security modes and two maximal
attack modes. All six inputs are required. -/
theorem exactStatement_of_basis
    (hd : XmssSufCmaSecure CountingMode.direct 122)
    (hk : XmssSufCmaSecure ⟨true, false, false, false⟩ 127)
    (hs : XmssSufCmaSecure ⟨false, true, false, false⟩ 127)
    (hv : XmssSufCmaSecure ⟨false, false, true, false⟩ 127)
    (ha122 : XmssSufCmaAttack ⟨false, false, false, true⟩ 122)
    (ha127 : XmssSufCmaEverythingAttackStatement) : XmssSufCmaExactStatement := by
  intro mode
  by_cases h : (mode.keygen || mode.signer || mode.verifier) = true
  · have hbits : conjecturedBits mode = 127 := by simp [conjecturedBits, h]
    rw [hbits]
    exact ⟨secure_127_of_minimal_modes hk hs hv mode h,
      not_hasClassicalSecurityBits_of_le (le_everything mode) xmss 128 ha127⟩
  · have hbits : conjecturedBits mode = 122 := by simp [conjecturedBits, h]
    rw [hbits]
    have hnone : mode.keygen = false ∧ mode.signer = false ∧ mode.verifier = false := by
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using h
    exact ⟨hasClassicalSecurityBits_of_le (direct_le mode) xmss 122 hd,
      not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le, hnone.1, hnone.2.1, hnone.2.2]) xmss 123 ha122⟩

/-- These six obligations are equivalent to the unchanged statement of the full conjecture. -/
theorem exactStatement_iff_basis : XmssSufCmaExactStatement ↔
    XmssSufCmaSecure CountingMode.direct 122 ∧
    XmssSufCmaSecure ⟨true, false, false, false⟩ 127 ∧
    XmssSufCmaSecure ⟨false, true, false, false⟩ 127 ∧
    XmssSufCmaSecure ⟨false, false, true, false⟩ 127 ∧
    XmssSufCmaAttack ⟨false, false, false, true⟩ 122 ∧
    XmssSufCmaEverythingAttackStatement := by
  constructor
  · intro h
    exact ⟨(h CountingMode.direct).1, (h ⟨true, false, false, false⟩).1,
      (h ⟨false, true, false, false⟩).1, (h ⟨false, false, true, false⟩).1,
      (h ⟨false, false, false, true⟩).2, (h CountingMode.everything).2⟩
  · rintro ⟨hd, hk, hs, hv, ha122, ha127⟩
    exact exactStatement_of_basis hd hk hs hv ha122 ha127

end XmssSecurity.Modes

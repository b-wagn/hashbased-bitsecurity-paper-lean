import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# A basis for the exact-security conjecture

Four lower bounds and two attacks suffice for all sixteen modes. In particular, the 122-bit
attack must allow charging signing requests: an attack proved only for `direct` does not by itself
give the upper bound for that larger mode.
-/

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open SUFCMA

theorem direct_le (mode : CountingMode) : CountingMode.direct.Le mode := by
  simp [CountingMode.Le, CountingMode.direct]

theorem le_everything (mode : CountingMode) : mode.Le CountingMode.everything := by
  simp [CountingMode.Le, CountingMode.everything]

/-- The three minimal modes charging an honest party cover every such counting mode. -/
theorem secure_127_of_minimal_modes
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (mode : CountingMode) (h : (mode.keygen || mode.signer || mode.verifier) = true) :
    (SUFCMA.notion mode).HasClassicalSecurityBits xmss 127 := by
  simp only [Bool.or_eq_true] at h
  rcases h with (hkeygen | hsigner) | hverifier
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hkeygen]) xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hsigner]) xmss 127 hs
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hverifier]) xmss 127 hv

/-- Assemble the exact-security picture from the four minimal security modes and two maximal
attack modes. All six inputs are required. -/
theorem exactStatement_of_basis
    (hd : (SUFCMA.notion CountingMode.direct).HasClassicalSecurityBits xmss 122)
    (hk : (SUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (SUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (ha122 : ¬(SUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1))
    (ha127 : ¬(SUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1)) : (∀ mode : SUFCMA.CountingMode, (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss (if mode.keygen || mode.signer || mode.verifier then 127 else 122)) := by
  intro mode
  by_cases h : (mode.keygen || mode.signer || mode.verifier) = true
  · rw [if_pos h]
    exact ⟨secure_127_of_minimal_modes hk hs hv mode h,
      not_hasClassicalSecurityBits_of_le (le_everything mode) xmss 128 ha127⟩
  · rw [if_neg h]
    have hnone : mode.keygen = false ∧ mode.signer = false ∧ mode.verifier = false := by
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using h
    exact ⟨hasClassicalSecurityBits_of_le (direct_le mode) xmss 122 hd,
      not_hasClassicalSecurityBits_of_le
        (by simp [CountingMode.Le, hnone.1, hnone.2.1, hnone.2.2]) xmss 123 ha122⟩

end XmssSecurity.TargetSum.Modes

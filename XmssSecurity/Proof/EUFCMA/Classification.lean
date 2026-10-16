import XmssSecurity.Proof.EUFCMA.Exact

/-! Five minimal security modes and two attacks characterize all sixteen
standard-unforgeability modes: direct-only has 126 bits, all others have 127. -/

namespace XmssSecurity.EUFCMA

open SUFCMA

theorem secure_127_of_minimal_modes
    (hk : (EUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (EUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (hr : (EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss 127)
    (mode : CountingMode) (h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true) :
    (EUFCMA.notion mode).HasClassicalSecurityBits xmss 127 := by
  simp only [Bool.or_eq_true] at h
  rcases h with ((hkeygen | hsigner) | hverifier) | hrequests
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hkeygen]) xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hsigner]) xmss 127 hs
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hverifier]) xmss 127 hv
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hrequests]) xmss 127 hr

theorem exactStatement_of_basis
    (hd : (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss 126)
    (hk : (EUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hs : (EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127)
    (hv : (EUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127)
    (hr : (EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss 127)
    (ha126 : ¬(EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss (126 + 1))
    (ha127 : ¬(EUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1)) : (∀ mode : SUFCMA.CountingMode, (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss (if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126)) := by
  intro mode
  by_cases h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true
  · rw [if_pos h]
    exact ⟨secure_127_of_minimal_modes hk hs hv hr mode h,
      not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 ha127⟩
  · rw [if_neg h]
    have hnone : mode.keygen = false ∧ mode.signer = false ∧ mode.verifier = false ∧ mode.requests = false := by
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using h
    have hmode : mode = CountingMode.direct := by
      cases mode
      simp_all [CountingMode.direct]
    subst mode
    exact ⟨hd, ha126⟩

theorem exactStatement_iff_basis : (∀ mode : SUFCMA.CountingMode, (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss (if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126)) ↔
    (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss 126 ∧
    (EUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits xmss 127 ∧
    (EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127 ∧
    (EUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits xmss 127 ∧
    (EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss 127 ∧
    ¬(EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss (126 + 1) ∧
    ¬(EUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1) := by
  constructor
  · intro h
    exact ⟨(h CountingMode.direct).1, (h ⟨true, false, false, false⟩).1,
      (h ⟨false, true, false, false⟩).1, (h ⟨false, false, true, false⟩).1,
      (h ⟨false, false, false, true⟩).1, (h CountingMode.direct).2, (h CountingMode.everything).2⟩
  · rintro ⟨hd, hk, hs, hv, hr, ha126, ha127⟩
    exact exactStatement_of_basis hd hk hs hv hr ha126 ha127

/-- info: 'XmssSecurity.EUFCMA.exactStatement_iff_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactStatement_iff_basis

end XmssSecurity.EUFCMA

import XmssSecurity.Proof.EUFCMA.Exact

/-! Five minimal security modes and two attacks characterize all sixteen
standard-unforgeability modes: direct-only has 126 bits, all others have 127. -/

namespace XmssSecurity.EUFCMA

open SUFCMA

theorem secure_127_of_minimal_modes
    (hk : XmssEufCmaSecure ⟨true, false, false, false⟩ 127)
    (hs : XmssEufCmaSecure ⟨false, true, false, false⟩ 127)
    (hv : XmssEufCmaSecure ⟨false, false, true, false⟩ 127)
    (hr : XmssEufCmaRequestsStatement)
    (mode : CountingMode) (h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true) :
    XmssEufCmaSecure mode 127 := by
  simp only [Bool.or_eq_true] at h
  rcases h with ((hkeygen | hsigner) | hverifier) | hrequests
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hkeygen]) xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hsigner]) xmss 127 hs
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hverifier]) xmss 127 hv
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hrequests]) xmss 127 hr

theorem exactStatement_of_basis
    (hd : XmssEufCmaDirectStatement)
    (hk : XmssEufCmaSecure ⟨true, false, false, false⟩ 127)
    (hs : XmssEufCmaSecure ⟨false, true, false, false⟩ 127)
    (hv : XmssEufCmaSecure ⟨false, false, true, false⟩ 127)
    (hr : XmssEufCmaRequestsStatement)
    (ha126 : XmssEufCmaDirectAttackStatement)
    (ha127 : XmssEufCmaEverythingAttackStatement) : XmssEufCmaExactStatement := by
  intro mode
  by_cases h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true
  · have hbits : eufCmaBits mode = 127 := by simp [eufCmaBits, h]
    rw [hbits]
    exact ⟨secure_127_of_minimal_modes hk hs hv hr mode h,
      not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 ha127⟩
  · have hbits : eufCmaBits mode = 126 := by simp [eufCmaBits, h]
    rw [hbits]
    have hnone : mode.keygen = false ∧ mode.signer = false ∧ mode.verifier = false ∧ mode.requests = false := by
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using h
    have hmode : mode = CountingMode.direct := by
      cases mode
      simp_all [CountingMode.direct]
    subst mode
    exact ⟨hd, ha126⟩

theorem exactStatement_iff_basis : XmssEufCmaExactStatement ↔
    XmssEufCmaDirectStatement ∧
    XmssEufCmaSecure ⟨true, false, false, false⟩ 127 ∧
    XmssEufCmaSecure ⟨false, true, false, false⟩ 127 ∧
    XmssEufCmaSecure ⟨false, false, true, false⟩ 127 ∧
    XmssEufCmaRequestsStatement ∧
    XmssEufCmaDirectAttackStatement ∧
    XmssEufCmaEverythingAttackStatement := by
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

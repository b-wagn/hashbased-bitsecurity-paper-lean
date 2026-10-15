import XmssSecurity.Statement.EUFCMAClaims
import XmssSecurity.Proof.EUFCMA.Modes
import XmssSecurity.Proof.Modes.Exact

/-! A minimal basis for the proposed standard-unforgeability classification:
127-bit direct-query security and an attack on 128 bits with everything charged. -/

namespace XmssSecurity.EUFCMA

open SUFCMA

theorem exactStatement_of_basis
    (hd : XmssEufCmaDirectStatement)
    (ha : XmssEufCmaEverythingAttackStatement) : XmssEufCmaExactStatement := by
  intro mode
  exact ⟨hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 127 hd,
    not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 ha⟩

theorem exactStatement_iff_basis : XmssEufCmaExactStatement ↔
    XmssEufCmaDirectStatement ∧ XmssEufCmaEverythingAttackStatement := by
  constructor
  · intro h
    exact ⟨(h CountingMode.direct).1, (h CountingMode.everything).2⟩
  · rintro ⟨hd, ha⟩
    exact exactStatement_of_basis hd ha

/-- info: 'XmssSecurity.EUFCMA.exactStatement_iff_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactStatement_iff_basis

end XmssSecurity.EUFCMA

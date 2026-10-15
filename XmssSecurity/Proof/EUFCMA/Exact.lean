import XmssSecurity.Statement.EUFCMAClaims
import XmssSecurity.Proof.EUFCMA.Modes
import XmssSecurity.Proof.Modes.Exact

/-! A basis for the initial uniform standard-unforgeability conjecture:
127-bit direct-query security and an attack on 128 bits with everything charged. -/

namespace XmssSecurity.EUFCMA

open SUFCMA

theorem uniform127Statement_of_basis
    (hd : XmssEufCmaDirect127Conjecture)
    (ha : XmssEufCmaEverythingAttackStatement) : XmssEufCmaUniform127Statement := by
  intro mode
  exact ⟨hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 127 hd,
    not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 ha⟩

theorem uniform127Statement_iff_basis : XmssEufCmaUniform127Statement ↔
    XmssEufCmaDirect127Conjecture ∧ XmssEufCmaEverythingAttackStatement := by
  constructor
  · intro h
    exact ⟨(h CountingMode.direct).1, (h CountingMode.everything).2⟩
  · rintro ⟨hd, ha⟩
    exact uniform127Statement_of_basis hd ha

/-- info: 'XmssSecurity.EUFCMA.uniform127Statement_iff_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform127Statement_iff_basis

end XmssSecurity.EUFCMA

import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Common.EUFCMA.Modes
import XmssSecurity.Proof.TargetSum.Modes.Exact
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-! A basis for the initial uniform standard-unforgeability conjecture:
127-bit direct-query security and an attack on 128 bits with everything charged. -/

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open SUFCMA hiding experiment game gameCounted notion securityGame

theorem uniform127Statement_of_basis
    (hd : (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss 127)
    (ha : ¬(EUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1)) : (∀ mode : SUFCMA.CountingMode, (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127) := by
  intro mode
  exact ⟨hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 127 hd,
    not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 ha⟩

theorem uniform127Statement_iff_basis : (∀ mode : SUFCMA.CountingMode, (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127) ↔
    (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss 127 ∧ ¬(EUFCMA.notion SUFCMA.CountingMode.everything).HasClassicalSecurityBits xmss (127 + 1) := by
  constructor
  · intro h
    exact ⟨(h CountingMode.direct).1, (h CountingMode.everything).2⟩
  · rintro ⟨hd, ha⟩
    exact uniform127Statement_of_basis hd ha

/-- info: 'XmssSecurity.TargetSum.EUFCMA.uniform127Statement_iff_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniform127Statement_iff_basis

end XmssSecurity.TargetSum.EUFCMA

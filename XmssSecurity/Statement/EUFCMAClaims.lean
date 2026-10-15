import XmssSecurity.Statement.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA

/-!
# Standard-unforgeability claims about XMSS

The target is exactly 127 bits of classical EUF-CMA security in all sixteen counting
modes. Unlike a strong forgery, a standard forgery cannot reuse a requested
epoch/message pair. The same-message chain-mutation attack therefore does not
give a 122-bit upper bound here. The neighboring-encoding attack uses a different
message and supplies the 127-bit upper bound.

These are statements, not assumptions: each milestone needs a kernel-checked proof.
The existing SUF-CMA statement and its exact-security theorem are unchanged.
-/

namespace XmssSecurity

/-- A lower bound on standard unforgeability under the selected counting mode. -/
abbrev XmssEufCmaSecure (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  (EUFCMA.notion mode).HasClassicalSecurityBits xmss bits

/-- An attack refuting one more bit of standard unforgeability. -/
abbrev XmssEufCmaAttack (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  ¬ (EUFCMA.notion mode).HasClassicalSecurityBits xmss (bits + 1)

/-- The proposed exact standard-unforgeability classification. -/
abbrev XmssEufCmaExactStatement : Prop :=
  ∀ mode : SUFCMA.CountingMode,
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127

/-- The direct-query lower bound is the minimal security basis obligation. -/
abbrev XmssEufCmaDirectStatement : Prop :=
  XmssEufCmaSecure SUFCMA.CountingMode.direct 127

/-- The maximal counting mode is the attack basis obligation. -/
abbrev XmssEufCmaEverythingAttackStatement : Prop :=
  XmssEufCmaAttack SUFCMA.CountingMode.everything 127

end XmssSecurity

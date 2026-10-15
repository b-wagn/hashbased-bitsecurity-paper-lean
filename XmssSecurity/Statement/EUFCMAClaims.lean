import XmssSecurity.Statement.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA

/-!
# Standard-unforgeability claims about XMSS

The initial target of exactly 127 bits in all sixteen counting modes is false:
the proof layer constructs a one-query replay/fallback attack against the direct-only
mode. Its lower bound is currently 125 bits and its upper bound 126 bits. Unlike a
strong forgery, a standard forgery cannot reuse a requested
epoch/message pair. The same-message chain-mutation attack therefore does not
give a 122-bit upper bound here. The neighboring-encoding attack uses a different
message and supplies the 127-bit upper bound.

The initial uniform target is retained below as a predicate that the proof layer
explicitly refutes. These are statements, not assumptions.
The existing SUF-CMA statement and its exact-security theorem are unchanged.
-/

namespace XmssSecurity

/-- A lower bound on standard unforgeability under the selected counting mode. -/
abbrev XmssEufCmaSecure (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  (EUFCMA.notion mode).HasClassicalSecurityBits xmss bits

/-- An attack refuting one more bit of standard unforgeability. -/
abbrev XmssEufCmaAttack (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  ¬ (EUFCMA.notion mode).HasClassicalSecurityBits xmss (bits + 1)

/-- The initial uniform 127-bit conjecture, now refuted in the proof layer. -/
abbrev XmssEufCmaExactStatement : Prop :=
  ∀ mode : SUFCMA.CountingMode,
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127

/-- The initial direct-query 127-bit conjecture, now refuted in the proof layer. -/
abbrev XmssEufCmaDirectStatement : Prop :=
  XmssEufCmaSecure SUFCMA.CountingMode.direct 127

/-- The maximal counting mode is the attack basis obligation. -/
abbrev XmssEufCmaEverythingAttackStatement : Prop :=
  XmssEufCmaAttack SUFCMA.CountingMode.everything 127

end XmssSecurity

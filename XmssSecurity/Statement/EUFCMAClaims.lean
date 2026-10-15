import XmssSecurity.Statement.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA

/-!
# Standard-unforgeability claims about XMSS

The exact classification is 126 bits for direct queries alone and 127 bits for
the other fifteen counting modes. A standard forgery cannot reuse a requested
epoch/message pair, including one whose request failed. The proof layer supplies
a one-query replay/fallback attack for the direct-only upper bound and a
neighboring-message attack for the 127-bit upper bound in the other modes.

The initial uniform target is retained below as a predicate that the proof layer
explicitly refutes. These are statements, not assumptions.
The existing SUF-CMA statement and its exact-security theorem are unchanged.
-/

namespace XmssSecurity

/-- Exact classical standard-unforgeability bits under each counting mode. -/
def eufCmaBits (mode : SUFCMA.CountingMode) : ℕ :=
  if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126

/-- A lower bound on standard unforgeability under the selected counting mode. -/
abbrev XmssEufCmaSecure (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  (EUFCMA.notion mode).HasClassicalSecurityBits xmss bits

/-- An attack refuting one more bit of standard unforgeability. -/
abbrev XmssEufCmaAttack (mode : SUFCMA.CountingMode) (bits : ℕ) : Prop :=
  ¬ (EUFCMA.notion mode).HasClassicalSecurityBits xmss (bits + 1)

/-- The complete standard-unforgeability classification for all sixteen modes. -/
abbrev XmssEufCmaExactStatement : Prop :=
  ∀ mode : SUFCMA.CountingMode,
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss (eufCmaBits mode)

/-- Standard unforgeability when only direct hash queries are charged. -/
abbrev XmssEufCmaDirectStatement : Prop :=
  XmssEufCmaSecure SUFCMA.CountingMode.direct 126

/-- A direct-only attack refuting 127-bit standard security. -/
abbrev XmssEufCmaDirectAttackStatement : Prop :=
  XmssEufCmaAttack SUFCMA.CountingMode.direct 126

/-- Standard security when direct hashes and signing requests are charged. -/
abbrev XmssEufCmaRequestsStatement : Prop :=
  XmssEufCmaSecure ⟨false, false, false, true⟩ 127

/-- The initial uniform 127-bit conjecture, refuted in the proof layer. -/
abbrev XmssEufCmaUniform127Statement : Prop :=
  ∀ mode : SUFCMA.CountingMode,
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127

/-- The initial direct-query 127-bit conjecture, refuted in the proof layer. -/
abbrev XmssEufCmaDirect127Conjecture : Prop :=
  XmssEufCmaSecure SUFCMA.CountingMode.direct 127

/-- The maximal counting mode is the attack basis obligation. -/
abbrev XmssEufCmaEverythingAttackStatement : Prop :=
  XmssEufCmaAttack SUFCMA.CountingMode.everything 127

end XmssSecurity

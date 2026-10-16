import XmssSecurity.Proof.Modes.QueryKinds
import XmssSecurity.Proof.Main.StrongUnforgeability
import XmssSecurity.Proof.EUFCMA.Reduction
import XmssSecurity.Proof.EUFCMA.NeighborAttack
import XmssSecurity.Proof.EUFCMA.Exact
import XmssSecurity.Proof.EUFCMA.DirectBridge
import XmssSecurity.Proof.EUFCMA.FreshAcceptancePrefix
import XmssSecurity.Proof.EUFCMA.ReferenceHop
import XmssSecurity.Proof.EUFCMA.DirectSecurity
import XmssSecurity.Proof.EUFCMA.ReplayFallback
import XmssSecurity.Proof.EUFCMA.ReplayAccounting
import XmssSecurity.Proof.EUFCMA.Direct126
import XmssSecurity.Proof.EUFCMA.RequestsBridge
import XmssSecurity.Proof.EUFCMA.RequestsExpected
import XmssSecurity.Proof.EUFCMA.RequestsActivity
import XmssSecurity.Proof.EUFCMA.RequestsTerminalFirstLane
import XmssSecurity.Proof.EUFCMA.RequestsEncodingCollision
import XmssSecurity.Proof.EUFCMA.ExpectedSecondLane
import XmssSecurity.Proof.EUFCMA.ExpectedDirectSeed
import XmssSecurity.Proof.EUFCMA.RequestsLoss
import XmssSecurity.Proof.EUFCMA.Requests127
import XmssSecurity.Proof.EUFCMA.Classification

/-!
# Assembly of the standard-unforgeability classification

Combines the five minimal security proofs and the two attacks into the exact classification
stated in `Statement/UnforgeabilityTheorems.lean`. The three honest-party modes inherit their
127-bit bounds from strong unforgeability. The import list above also keeps every proof module
of the development in the default build.
-/

namespace XmssSecurity.Proof

open SUFCMA

theorem eufCma_exact (mode : CountingMode) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits xmss
      (if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126) :=
  EUFCMA.exactStatement_of_basis EUFCMA.direct_126
    (EUFCMA.security_of_strong _ xmss 127 Modes.sufCmaKeygen_127)
    (EUFCMA.security_of_strong _ xmss 127 Modes.sufCmaSigner_127)
    (EUFCMA.security_of_strong _ xmss 127 Modes.sufCmaVerifier_127)
    EUFCMA.Requests.secure_127 EUFCMA.replay_direct_attack_126
    Attack.neighbor_euf_everything_attack mode

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem eufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z ∨
        QueryKind.sign ∈ Z then 127 else 126) := by
  rw [Modes.eufHasExactClassicalSecurityBits_iff Z hZ]
  have hbits : (if (Modes.modeOf Z).keygen || (Modes.modeOf Z).signer ||
      (Modes.modeOf Z).verifier || (Modes.modeOf Z).requests then 127 else 126) =
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z ∨
        QueryKind.sign ∈ Z then 127 else 126) := by
    simp [Modes.modeOf, or_assoc]
  rw [← hbits]
  exact eufCma_exact (Modes.modeOf Z)

end XmssSecurity.Proof

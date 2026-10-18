import XmssSecurity.Proof.Common.Modes.QueryKinds
import XmssSecurity.Proof.TargetSum.Main.StrongUnforgeability
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.TargetSum.EUFCMA.NeighborAttack
import XmssSecurity.Proof.Generic.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Common.EUFCMA.Modes
import XmssSecurity.Proof.Generic.Modes.Exact
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA
import XmssSecurity.Proof.TargetSum.EUFCMA.DirectBridge
import XmssSecurity.Proof.TargetSum.EUFCMA.FreshAcceptancePrefix
import XmssSecurity.Proof.TargetSum.EUFCMA.ReferenceHop
import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayFallback
import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayAccounting
import XmssSecurity.Proof.TargetSum.EUFCMA.Direct126
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsBridge
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsExpected
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsActivity
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsTerminalFirstLane
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsEncodingCollision
import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedSecondLane
import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedDirectSeed
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsLoss
import XmssSecurity.Proof.TargetSum.EUFCMA.Requests127
import XmssSecurity.Proof.TargetSum.EUFCMA.Classification
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-!
# Assembly of the standard-unforgeability classification

Combines the five minimal security proofs and the two attacks into the exact classification
stated in `Statement/UnforgeabilityTheorems.lean`. The three honest-party modes inherit their
127-bit bounds from strong unforgeability. The import list above also keeps every proof module
of the development in the default build.
-/

namespace XmssSecurity.TargetSum.Proof

open SUFCMA

theorem eufCma_exact (mode : CountingMode) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss
      (if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126) :=
  EUFCMA.exactStatement_of_basis EUFCMA.direct_126
    (EUFCMA.security_of_strong _ Generic.xmss 127 Modes.sufCmaKeygen_127)
    (EUFCMA.security_of_strong _ Generic.xmss 127 Modes.sufCmaSigner_127)
    (EUFCMA.security_of_strong _ Generic.xmss 127 Modes.sufCmaVerifier_127)
    EUFCMA.Requests.secure_127 EUFCMA.replay_direct_attack_126
    Attack.neighbor_euf_everything_attack mode

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem lossyEufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.lossyGame).HasExactClassicalSecurityBits Generic.xmss Z
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

end XmssSecurity.TargetSum.Proof

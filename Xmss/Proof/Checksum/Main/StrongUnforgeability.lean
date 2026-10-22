import Xmss.Proof.Common.Modes.QueryKinds
import Xmss.Proof.Checksum.Modes.Classification
import Xmss.Proof.Common.Modes.Direct
import Xmss.Proof.Checksum.Modes.Keygen
import Xmss.Proof.Checksum.Modes.Verifier
import Xmss.Proof.Checksum.Signer.Security
import Xmss.Proof.Checksum.Direct.DecidingSecurity
import Xmss.Proof.Checksum.Attack.ChainMutationSigner
import Xmss.Proof.Checksum.Attack.NeighborAccounting
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-!
# Assembly of the strong-unforgeability classification

Combines the five minimal security proofs and the four attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`.
-/

namespace Xmss.Checksum

open Unforgeability SUFCMA

theorem sufCma_exact (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss (Modes.exactLevel mode) :=
  Modes.exactStatement_of_checksumBasis
    ((Modes.notion_direct_hasClassicalSecurityBits_iff Generic.xmss 122).2 Direct.sufCmaDirect_122)
    Modes.sufCmaKeygen_127 Modes.sufCmaVerifier_127 Modes.sufCmaSigner_123 Modes.sufCmaSignerRequests_124
    Attack.chainMutation_requests_attack
    Attack.chainMutation_signer_attack
    Attack.chainMutation_signerRequests_attack
    Attack.neighbor_everything_attack mode

theorem exactLevel_modeOf (Z : Finset QueryKind) :
    Modes.exactLevel (Modes.modeOf Z) =
      if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z then (if QueryKind.sign ∈ Z then 124 else 123)
      else 122 := by
  simp only [Modes.exactLevel, Modes.modeOf, Bool.or_eq_true, decide_eq_true_eq]

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem lossySufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.lossyGame).HasExactClassicalSecurityBits Generic.xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z then (if QueryKind.sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Modes.hasExactClassicalSecurityBits_iff Z hZ, ← exactLevel_modeOf]
  exact sufCma_exact (Modes.modeOf Z)

end Xmss.Checksum

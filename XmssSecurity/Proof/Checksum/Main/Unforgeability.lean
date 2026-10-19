import XmssSecurity.Proof.Checksum.Main.StrongUnforgeability
import XmssSecurity.Proof.Checksum.EUFCMA.NeighborAttack
import XmssSecurity.Proof.Checksum.EUFCMA.FreshMessageAttack
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-!
# Assembly of the standard-unforgeability classification

Combines the five minimal security proofs of strong unforgeability, which standard unforgeability
inherits, and four standard attacks into the exact classification stated in
`Statement/UnforgeabilityTheorems.lean`.
-/

namespace XmssSecurity.Checksum.Proof

open SUFCMA

theorem eufCma_exact (mode : CountingMode) :
    (EUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss (Modes.exactLevel mode) :=
  Modes.eufExactStatement_of_checksumBasis
    ((Modes.notion_direct_hasClassicalSecurityBits_iff Generic.xmss 122).2 Direct.sufCmaDirect_122)
    Modes.sufCmaKeygen_127 Modes.sufCmaVerifier_127 Modes.sufCmaSigner_123 Modes.sufCmaSignerRequests_124
    Attack.freshMessage_requests_attack
    Attack.freshMessage_signer_attack
    Attack.freshMessage_signerRequests_attack
    Attack.neighbor_euf_everything_attack mode

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem lossyEufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (EUFCMA.lossyGame).HasExactClassicalSecurityBits Generic.xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z then (if QueryKind.sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Modes.eufHasExactClassicalSecurityBits_iff Z hZ, ← exactLevel_modeOf]
  exact eufCma_exact (Modes.modeOf Z)

end XmssSecurity.Checksum.Proof

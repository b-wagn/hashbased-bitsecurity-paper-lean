import XmssSecurity.Proof.Modes.QueryKinds
import XmssSecurity.Proof.Modes.Classification
import XmssSecurity.Proof.Modes.Direct
import XmssSecurity.Proof.Modes.Keygen
import XmssSecurity.Proof.Modes.Verifier
import XmssSecurity.Proof.Signer.Security
import XmssSecurity.Proof.Direct.DecidingSecurity
import XmssSecurity.Proof.Attack.ChainMutationSigner
import XmssSecurity.Proof.Attack.NeighborAccounting

/-!
# Assembly of the strong-unforgeability classification

Combines the five minimal security proofs and the four attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`.
-/

namespace XmssSecurity.Proof

open SUFCMA

theorem sufCma_exact (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss (Modes.exactLevel mode) :=
  Modes.exactStatement_of_checksumBasis
    ((Modes.notion_direct_hasClassicalSecurityBits_iff xmss 122).2 Direct.sufCmaDirect_122)
    Modes.sufCmaKeygen_127 Modes.sufCmaVerifier_127 Modes.sufCmaSigner_123
    Modes.sufCmaSignerRequests_124 Attack.chainMutation_requests_attack
    Attack.chainMutation_signer_attack Attack.chainMutation_signerRequests_attack
    Attack.neighbor_everything_attack mode

theorem exactLevel_modeOf (Z : Finset QueryKind) :
    Modes.exactLevel (Modes.modeOf Z) =
      if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122 := by
  simp only [Modes.exactLevel, Modes.modeOf, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem sufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.verifier ∈ Z then 127
      else if QueryKind.signer ∈ Z ∧ QueryKind.sign ∈ Z then 124
      else if QueryKind.signer ∈ Z then 123
      else 122) := by
  rw [Modes.hasExactClassicalSecurityBits_iff Z hZ, ← exactLevel_modeOf]
  exact sufCma_exact (Modes.modeOf Z)

end XmssSecurity.Proof

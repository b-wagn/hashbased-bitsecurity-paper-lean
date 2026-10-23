import Xmss.Statement.BitSecurity
import Xmss.Statement.UnforgeabilityGame
import Xmss.Statement.Scheme.TargetSum
import Xmss.Statement.Scheme.Checksum
import Xmss.Proof.TargetSum.Main.PaperGames
import Xmss.Proof.TargetSum.Scheme.Bridge
import Xmss.Proof.Checksum.Main.PaperGames
import Xmss.Proof.Checksum.Scheme.Bridge

/-!
# Standard unforgeability (EUF-CMA) of XMSS: the theorems
-/

open scoped ENNReal

namespace Xmss

open Unforgeability

/-- Target sum: 126 bits for direct hashes alone; 127 if any other query kind is counted. -/
theorem xmssTargetSum_eufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    EUFCMA.securityGame.HasExactClassicalSecurityBits xmssTargetSum Z
      (if Z = {.hash} then 126 else 127) := by
  rw [TargetSum.xmssTargetSum_eq]
  convert TargetSum.eufCma_exact_of_hash_mem Z hZ using 1 <;> first | rfl | decide +revert

/-- Checksum: 127 bits with keygen or verification counted; otherwise 122, 123, or 124. -/
theorem xmssChecksum_eufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    EUFCMA.securityGame.HasExactClassicalSecurityBits xmssChecksum Z
      (if .keygen ∈ Z ∨ .verifier ∈ Z then 127
      else if .signer ∈ Z then (if .sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.eufCma_exact_of_hash_mem Z hZ

/-- info: 'Xmss.xmssTargetSum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_eufCma_exact

/-- info: 'Xmss.xmssChecksum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_eufCma_exact

end Xmss

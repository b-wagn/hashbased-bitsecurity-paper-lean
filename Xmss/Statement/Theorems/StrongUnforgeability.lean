import Xmss.Statement.BitSecurity
import Xmss.Statement.UnforgeabilityGame
import Xmss.Statement.Scheme.TargetSum
import Xmss.Statement.Scheme.Checksum
import Xmss.Proof.TargetSum.Main.PaperGames
import Xmss.Proof.TargetSum.Scheme.Bridge
import Xmss.Proof.Checksum.Main.PaperGames
import Xmss.Proof.Checksum.Scheme.Bridge

/-!
# Strong unforgeability (SUF-CMA) of XMSS: the theorems
-/

open scoped ENNReal

namespace Xmss

open Unforgeability SUFCMA

/-- Target sum: 122 bits if only adversary queries are counted; 127 otherwise. -/
theorem xmssTargetSum_sufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    SUFCMA.securityGame.HasExactClassicalSecurityBits xmssTargetSum Z
      (if Z ⊆ {.hash, .sign} then 122 else 127) := by
  rw [TargetSum.xmssTargetSum_eq]
  convert TargetSum.sufCma_exact_of_hash_mem Z hZ using 1 <;> first | rfl | decide +revert

/-- Checksum: 127 bits with keygen or verification counted; otherwise 122, 123, or 124. -/
theorem xmssChecksum_sufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    SUFCMA.securityGame.HasExactClassicalSecurityBits xmssChecksum Z
      (if .keygen ∈ Z ∨ .verifier ∈ Z then 127
      else if .signer ∈ Z then (if .sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.sufCma_exact_of_hash_mem Z hZ

/-- info: 'Xmss.xmssTargetSum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_sufCma_exact

/-- info: 'Xmss.xmssChecksum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_sufCma_exact

end Xmss

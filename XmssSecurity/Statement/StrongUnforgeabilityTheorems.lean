import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.SUFCMA
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.Main.PaperGames
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Main.SignerRequests
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Strong unforgeability of XMSS: the theorems

SUF-CMA bounds for both encodings and all sixteen counting modes containing `hash`.
Both encodings have exact integer levels throughout.
An exact level `b` means security at `b` and an attack against `b + 1` (`BitSecurity.lean`).
See the README for the results table and the manuscript for the attack descriptions.
-/

open scoped ENNReal

namespace XmssSecurity

open SUFCMA

/-- Target sum: 122 bits if only adversary queries are counted; 127 otherwise. -/
theorem xmssTargetSum_sufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    SUFCMA.securityGame.HasExactClassicalSecurityBits xmssTargetSum Z
      (if Z ⊆ {.hash, .sign} then 122 else 127) := by
  rw [TargetSum.xmssTargetSum_eq]
  convert TargetSum.Proof.sufCma_exact_of_hash_mem Z hZ using 1 <;> first | rfl | decide +revert

/-- Checksum: 127 bits with keygen or verification counted; otherwise 122, 123, or 124. -/
theorem xmssChecksum_sufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    SUFCMA.securityGame.HasExactClassicalSecurityBits xmssChecksum Z
      (if .keygen ∈ Z ∨ .verifier ∈ Z then 127
      else if .signer ∈ Z then (if .sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.sufCma_exact_of_hash_mem Z hZ

/-- Checksum with signer hashes and requests charged: between 124 and about 124.59 bits,
with a formally proved gap smaller than one bit. -/
theorem xmssChecksum_sufCma_signerRequests_bounds :
    SUFCMA.securityGame.HasTightClassicalSecurityBounds xmssChecksum {.hash, .signer, .sign}
      ((2 ^ 124 : ℕ) : ℝ≥0∞) (((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.sufCma_signerRequests_bounds

/-- info: 'XmssSecurity.xmssChecksum_sufCma_signerRequests_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_sufCma_signerRequests_bounds

/-- info: 'XmssSecurity.xmssTargetSum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_sufCma_exact

/-- info: 'XmssSecurity.xmssChecksum_sufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_sufCma_exact

end XmssSecurity

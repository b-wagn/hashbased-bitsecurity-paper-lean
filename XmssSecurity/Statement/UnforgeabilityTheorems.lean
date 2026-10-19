import XmssSecurity.Statement.BitSecurity
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.Main.PaperGames
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Main.SignerRequests
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Standard unforgeability of XMSS: the theorems

EUF-CMA bounds for both encodings and all sixteen counting modes containing `hash`.
Both encodings have exact integer levels throughout.
The forgery's epoch/message pair must be absent from `Signed` (`Security/EUFCMA.lean`).
See the README for the results table and the manuscript for the attack descriptions.
-/

open scoped ENNReal

namespace XmssSecurity

open SUFCMA

/-- Target sum: 126 bits for direct hashes alone; 127 if any other query kind is counted. -/
theorem xmssTargetSum_eufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    EUFCMA.securityGame.HasExactClassicalSecurityBits xmssTargetSum Z
      (if Z = {.hash} then 126 else 127) := by
  rw [TargetSum.xmssTargetSum_eq]
  convert TargetSum.Proof.eufCma_exact_of_hash_mem Z hZ using 1 <;> first | rfl | decide +revert

/-- Checksum: the same exact levels as SUF-CMA. -/
theorem xmssChecksum_eufCma_exact (Z : Finset QueryKind) (hZ : .hash ∈ Z) :
    EUFCMA.securityGame.HasExactClassicalSecurityBits xmssChecksum Z
      (if .keygen ∈ Z ∨ .verifier ∈ Z then 127
      else if .signer ∈ Z then (if .sign ∈ Z then 124 else 123)
      else 122) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.eufCma_exact_of_hash_mem Z hZ

/-- Checksum with signer hashes and requests charged: between 124 and about 124.59 bits,
with a formally proved gap smaller than one bit. -/
theorem xmssChecksum_eufCma_signerRequests_bounds :
    EUFCMA.securityGame.HasTightClassicalSecurityBounds xmssChecksum {.hash, .signer, .sign}
      ((2 ^ 124 : ℕ) : ℝ≥0∞) (((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32) := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Proof.eufCma_signerRequests_bounds

/-- info: 'XmssSecurity.xmssChecksum_eufCma_signerRequests_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_eufCma_signerRequests_bounds

/-- info: 'XmssSecurity.xmssTargetSum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_eufCma_exact

/-- info: 'XmssSecurity.xmssChecksum_eufCma_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_eufCma_exact

end XmssSecurity

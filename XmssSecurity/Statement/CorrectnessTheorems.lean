import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.CorrectnessError
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Correctness
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Correctness of XMSS: the theorems

This file states and proves the correctness of XMSS with both WOTS encodings in the random-oracle
model, for the correctness experiment of `Security/Correctness.lean`.

* With the checksummed encoding (`xmssChecksum`, `Scheme/Checksum.lean`) the correctness error is
  `0`. Every signing request for a fresh epoch is answered by a signature that verifies, whatever
  the adversary queries: every digest decodes, so the single randomizer trial succeeds, and the
  verifier recomputes the chain ends, the leaf, and the authentication path from the hash calls of
  key generation.
* With the target-sum encoding (`xmssTargetSum`, `Scheme/TargetSum.lean`) the correctness error
  is at most `2^-64864`. A signature that the signer returns verifies, as above, so the flag is
  set only when all `A_max = 2^32` randomizer trials of a request fail. For a fixed public
  parameter, master seed, epoch, and message, the oracle answers of these trials show this with
  probability at most `(1 - p + A_max / 2^192)^A_max ≤ 2^-(2^16)`, where `p > 2^-15` is the
  probability that a uniform digest decodes, whatever the adversary queries. A union bound over
  the `2^672` such tuples gives the bound.
-/

namespace XmssSecurity

/-- XMSS with the target-sum encoding has correctness error at most `2^-64864`. -/
theorem xmssTargetSum_correct : Correctness.HasCorrectnessError xmssTargetSum (1 / 2 ^ 64864) := by
  rw [TargetSum.xmssTargetSum_eq]
  exact TargetSum.Correct.correctnessError_le

/-- info: 'XmssSecurity.xmssTargetSum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_correct

/-- XMSS with the checksummed encoding has correctness error `0`. -/
theorem xmssChecksum_correct : Correctness.HasCorrectnessError xmssChecksum 0 := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Correct.correctnessError_zero

/-- info: 'XmssSecurity.xmssChecksum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_correct

end XmssSecurity

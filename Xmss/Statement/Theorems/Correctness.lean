import Xmss.Statement.CorrectnessGame
import Xmss.Statement.Scheme.TargetSum
import Xmss.Statement.Scheme.Checksum
import Xmss.Proof.TargetSum.CorrectnessError
import Xmss.Proof.TargetSum.Scheme.Bridge
import Xmss.Proof.Checksum.Correctness
import Xmss.Proof.Checksum.Scheme.Bridge

/-!
# Correctness of XMSS: the theorems
-/

namespace Xmss

/-- XMSS with the target-sum encoding has correctness error at most `2^-256`. -/
theorem xmssTargetSum_correct : Correctness.HasCorrectnessError xmssTargetSum (1 / 2 ^ 256) := by
  rw [TargetSum.xmssTargetSum_eq]
  exact TargetSum.Correctness.correctnessError_paper

/-- info: 'Xmss.xmssTargetSum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssTargetSum_correct

/-- XMSS with the checksummed encoding has correctness error `0`. -/
theorem xmssChecksum_correct : Correctness.HasCorrectnessError xmssChecksum 0 := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Correctness.correctnessError_zero

/-- info: 'Xmss.xmssChecksum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_correct

end Xmss

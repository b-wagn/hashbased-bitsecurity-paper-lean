import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Statement.Scheme.TargetSum
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.TargetSum.CorrectnessError
import XmssSecurity.Proof.TargetSum.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Correctness
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Correctness of XMSS: the theorems

Correctness error is at most `2^-64864` for target sum and zero for checksum.
The experiment in `Security/Correctness.lean` allows adaptive requests and unlimited hash queries.
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

import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Statement.Scheme.Checksum
import XmssSecurity.Proof.Checksum.Correctness
import XmssSecurity.Proof.Checksum.Scheme.Bridge

/-!
# Correctness of XMSS: the theorem

This file states and proves the correctness of XMSS with the WOTS encoding with a checksum
(`xmssChecksum`, `Scheme/Checksum.lean`) in the random-oracle model, for the correctness experiment
of `Security/Correctness.lean`: the correctness error is `0`. Every signing request for a fresh
epoch is answered by a signature that verifies, whatever the adversary queries: every digest
decodes, so the single randomizer trial succeeds, and the verifier recomputes the chain ends, the
leaf, and the authentication path from the hash calls of key generation.
-/

namespace XmssSecurity

/-- XMSS with the checksummed encoding has correctness error `0`. -/
theorem xmssChecksum_correct : Correctness.HasCorrectnessError xmssChecksum 0 := by
  rw [Checksum.xmssChecksum_eq]
  exact Checksum.Correct.correctnessError_zero

/-- info: 'XmssSecurity.xmssChecksum_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmssChecksum_correct

end XmssSecurity

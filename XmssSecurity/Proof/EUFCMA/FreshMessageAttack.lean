import XmssSecurity.Proof.Attack.ChainMutationSigner
import XmssSecurity.Proof.EUFCMA.Reduction

/-!
# Standard forgeries on a fresh message

TODO (work in progress): the adversary that requests one signature and submits it for a fresh
message refutes `123`, `124`, and `125` bits of standard unforgeability in the modes charging the
requests, the signer, and both.
-/

namespace XmssSecurity.Attack

open SUFCMA

theorem freshMessage_requests_attack :
    ¬(EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits xmss (122 + 1) := by
  sorry

theorem freshMessage_signer_attack :
    ¬(EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss (123 + 1) := by
  sorry

theorem freshMessage_signerRequests_attack :
    ¬(EUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits xmss (124 + 1) := by
  sorry

end XmssSecurity.Attack

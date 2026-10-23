import SlhDsaSecurity.Statement.CorrectnessGame
import SlhDsaSecurity.Proof.Correctness.SharedROM

/-!
# Correctness of SLH-DSA-SHAKE-128s: the theorems

Against one shared lazy random oracle, with actual randomized key generation: every request with a
valid context verifies with probability one, and every other request is rejected by the signer
with probability one. The correctness error is `0`.
-/

namespace SlhDsaSecurity

open CorrectnessGame

/-- **A valid request always verifies.** -/
theorem slhDsa_correct (request : Message) (hcontext : request.context.length ≤ 255) :
    Pr[fun result => result = some true |
      Xmss.RandomOracleModel.run (experiment request)] = 1 :=
  Correctness.SharedROM.valid_context_probability_one request hcontext

/-- **A request with an over-long context is always rejected by the signer.** -/
theorem slhDsa_rejects_long_context (request : Message) (hcontext : 255 < request.context.length) :
    Pr[fun result => result = none |
      Xmss.RandomOracleModel.run (experiment request)] = 1 :=
  Correctness.SharedROM.invalid_context_probability_one request hcontext

/-- info: 'SlhDsaSecurity.slhDsa_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_correct

/-- info: 'SlhDsaSecurity.slhDsa_rejects_long_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_rejects_long_context

end SlhDsaSecurity

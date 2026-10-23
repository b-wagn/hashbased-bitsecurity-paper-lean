import «SLH-DSA-SHAKE-128s».Statement.Security
import «SLH-DSA-SHAKE-128s».Proof.WorkFinal

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**, counting the adversary's
signing requests, its hash calls and the verification of its forgery. -/
theorem slhDsa_sufCma_127 : HasSecurityBits adversaryWork 127 :=
  WorkFinal.hasSecurityBits_work

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_127

end SlhDsaSecurity

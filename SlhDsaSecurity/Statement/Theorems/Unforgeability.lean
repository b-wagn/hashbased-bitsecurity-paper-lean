import SlhDsaSecurity.Statement.Security
import SlhDsaSecurity.Proof.ShareFinal
import SlhDsaSecurity.Proof.Security

/-!
# Standard unforgeability (EUF-CMA) of SLH-DSA-SHAKE-128s: the theorem

Same game and budget as the strong notion; the forgery need only be on a message never signed.
A standard forgery is a strong one, so the bound carries over.
-/

open scoped ENNReal

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of standard unforgeability, all hash calls counted.** -/
theorem slhDsa_eufCma_total_127 : HasTotalSecurityBits .standard 127 :=
  total_strong_implies_standard 127 ShareFinal.hasTotalSecurityBits_strong_127

/-- info: 'SlhDsaSecurity.slhDsa_eufCma_total_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_eufCma_total_127

end SlhDsaSecurity

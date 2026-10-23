import SlhDsaSecurity.Statement.Security
import SlhDsaSecurity.Proof.ShareFinal

/-!
# Strong unforgeability (SUF-CMA) of SLH-DSA-SHAKE-128s: the theorem

Every hash call of the game is counted — key generation, signing, the adversary's own, and final
verification — and the adversary may make up to `signingLimit` signing requests. For every
budget `q ≥ 1` bounding that total with probability one, a forgery that is new as a
request–signature pair succeeds with probability at most `q / 2^127`.
-/

open scoped ENNReal

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability, all hash calls counted.** -/
theorem slhDsa_sufCma_total_127 : HasTotalSecurityBits .strong 127 :=
  ShareFinal.hasTotalSecurityBits_strong_127

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_total_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_total_127

end SlhDsaSecurity

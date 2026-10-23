import «SLH-DSA-SHAKE-128s».Statement.SecurityBySource
import «SLH-DSA-SHAKE-128s».Proof.WorkFinal

/-!
# Strong unforgeability (SUF-CMA) of SLH-DSA-SHAKE-128s: the theorem

The scheme is pure, deterministic SLH-DSA at the 128s parameter set, with the SHAKE
instantiation's input formats (FIPS 205 §11.1, 32-byte addresses) and every hash function
idealized as one shared lazily sampled random oracle.

The game is `Xmss.SecurityGame` counting hash calls by source — signing requests, the
adversary's own calls, key generation's, the signer's and final verification's — and the
counting mode is the adversary's own work: its signing requests, its own hash calls, and the
verification of its forgery. Key generation's and the signer's hash calls are free. The adversary
stays within FIPS 205's limit of `2 ^ 64` signing requests. For every budget `q ≥ 1` bounding
the counted work with probability one, a forgery that is new as a request–signature pair
succeeds with probability at most `q / 2^127`.

Verifying a well-formed forgery costs at least `569` hash calls, so the bound is only nontrivial
for adversaries whose counted work is at least that.
-/

open scoped ENNReal

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**, counting the adversary's own
work: its signing requests, its own hash calls and the verification of its forgery. -/
theorem slhDsa_sufCma_127 : HasLimitedSecurityBits .strong adversaryWork 127 :=
  WorkFinal.hasLimitedSecurityBits_strong_work

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_127

end SlhDsaSecurity

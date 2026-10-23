import SlhDsaSecurity.Statement.SecurityBySource
import SlhDsaSecurity.Proof.BySourceTarget

/-!
# Strong unforgeability (SUF-CMA) of SLH-DSA-SHAKE-128s: the theorem

The game is `Xmss.SecurityGame` counting hash calls by source — signing requests, the
adversary's own calls, key generation's, the signer's and final verification's — and the
counting mode is every source but the signer. The adversary stays within FIPS 205's limit of
`2 ^ 64` signing requests. For every budget `q ≥ 1` bounding the counted work with probability
one, a forgery that is new as a request–signature pair succeeds with probability at most
`q / 2^127`.
-/

open scoped ENNReal

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**, every hash call counted but
the signer's own. -/
theorem slhDsa_sufCma_allButSigner_127 : HasLimitedSecurityBits .strong allButSigner 127 :=
  BySourceTarget.hasLimitedSecurityBits_strong_127

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_allButSigner_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_allButSigner_127

end SlhDsaSecurity

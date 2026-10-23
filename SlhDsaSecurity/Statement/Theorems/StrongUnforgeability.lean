import SlhDsaSecurity.Statement.Security
import SlhDsaSecurity.Statement.SecurityNoVerify
import SlhDsaSecurity.Statement.SecurityBySource
import SlhDsaSecurity.Proof.ShareFinal
import SlhDsaSecurity.Proof.NoVerifyTarget
import SlhDsaSecurity.Proof.BySourceTarget

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

/-- **The same, with final verification's hash calls not counted.** Key generation, signing and
the adversary's own calls are charged; any adversary within a total budget is within this one,
so this is the stronger statement. -/
theorem slhDsa_sufCma_noVerify_127 : HasNoVerifySecurityBits .strong 127 :=
  NoVerifyTarget.hasNoVerifySecurityBits_strong_127

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_total_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_total_127

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_noVerify_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_noVerify_127

/-- **The same in the main development's framework, with the signer's hash calls not counted.**
The game is `Xmss.SecurityGame` counting by source; the counting mode is every source but the
signer — requests, the adversary's own calls, key generation's and final verification's — and
adversaries stay within FIPS 205's signing limit. -/
theorem slhDsa_sufCma_allButSigner_127 : HasLimitedSecurityBits .strong allButSigner 127 :=
  BySourceTarget.hasLimitedSecurityBits_strong_127

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_allButSigner_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_allButSigner_127

end SlhDsaSecurity

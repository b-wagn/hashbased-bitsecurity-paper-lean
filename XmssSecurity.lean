import XmssSecurity.Statement.Claims
import XmssSecurity.Proof.Adversary.Security
import XmssSecurity.Proof.Direct.Assemble
import XmssSecurity.Proof.Direct.DecidingAssemble
import XmssSecurity.Proof.Direct.DecidingSecurity
import XmssSecurity.Proof.Direct.EncodingPrehit
import XmssSecurity.Proof.Direct.LargeBudget
import XmssSecurity.Proof.Modes.Direct
import XmssSecurity.Proof.Modes.AllHashes
import XmssSecurity.Proof.Modes.Lattice
import XmssSecurity.Proof.Modes.Projection
import XmssSecurity.Proof.Modes.Exact
import XmssSecurity.Proof.Modes.Keygen
import XmssSecurity.Proof.Modes.Verifier
import XmssSecurity.Proof.EncodingProbability
import XmssSecurity.Proof.EncodingRejectionProbability
import XmssSecurity.Proof.FreshPathProbability
import XmssSecurity.Proof.Attack.PathBounds
import XmssSecurity.Proof.Attack.ChainMutation
import XmssSecurity.Proof.Attack.ChainMutationAccounting
import XmssSecurity.Proof.Attack.MutationPath
import XmssSecurity.Proof.Attack.MutationProbability
import XmssSecurity.Proof.Attack.MutationSigningCache
import XmssSecurity.Proof.Attack.MutationVerification
import XmssSecurity.Proof.Attack.MutationAverage
import XmssSecurity.Proof.Attack.MutationGame

/-!
# Security of XMSS in the random-oracle model

The main theorems. Each proves a claim of `Statement/Claims.lean`; the statements (the scheme,
the security notion with its counting modes, and bit security) live under `Statement/`, the
proofs under `Proof/`.

The lattice of counting modes (`Proof/Modes/Lattice.lean`) spreads the proved levels to the
other modes: 122 bits holds in every mode, and 127 bits holds in every mode charging key generation
or verification.
-/



namespace XmssSecurity

open SUFCMA

/-- XMSS has 127 bits of classical SUF-CMA security, counting every hash call of the experiment. -/
theorem xmss_sufCma_allHashes_127 : XmssSufCmaAllHashesStatement :=
  (Modes.notion_allHashes_hasClassicalSecurityBits_iff xmss 127).2 Security.security127

/-- info: 'XmssSecurity.xmss_sufCma_allHashes_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_allHashes_127

/-- XMSS has 119 bits of classical SUF-CMA security, counting only the adversary's own hash
calls. -/
theorem xmss_sufCma_direct_119 : XmssSufCmaDirectStatement :=
  (Modes.notion_direct_hasClassicalSecurityBits_iff xmss 119).2 Direct.sufCmaDirect_119

/-- info: 'XmssSecurity.xmss_sufCma_direct_119' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_direct_119

/-- The deciding-path collision bound strengthens the direct guarantee to 120 bits. -/
theorem xmss_sufCma_direct_120 : XmssSufCmaSecure CountingMode.direct 120 :=
  (Modes.notion_direct_hasClassicalSecurityBits_iff xmss 120).2 Direct.sufCmaDirect_120

/-- info: 'XmssSecurity.xmss_sufCma_direct_120' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_direct_120

/-- The strengthened direct guarantee transfers to every counting mode. -/
theorem xmss_sufCma_secure_120 (mode : CountingMode) : XmssSufCmaSecure mode 120 :=
  Modes.hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 120 xmss_sufCma_direct_120

/-- The single deciding probe and deciding-path collision bound give 122-bit direct security. -/
theorem xmss_sufCma_direct_122 : XmssSufCmaSecure CountingMode.direct 122 :=
  (Modes.notion_direct_hasClassicalSecurityBits_iff xmss 122).2 Direct.sufCmaDirect_122

/-- info: 'XmssSecurity.xmss_sufCma_direct_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_direct_122

/-- Every counting mode inherits the completed 122-bit direct-query guarantee. -/
theorem xmss_sufCma_secure_122 (mode : CountingMode) : XmssSufCmaSecure mode 122 :=
  Modes.hasClassicalSecurityBits_of_le (Modes.direct_le mode) xmss 122 xmss_sufCma_direct_122

/-- Charging direct queries and key generation gives 127-bit security. -/
theorem xmss_sufCma_keygen_127 : XmssSufCmaSecure ⟨true, false, false, false⟩ 127 :=
  Modes.sufCmaKeygen_127

/-- info: 'XmssSecurity.xmss_sufCma_keygen_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_keygen_127

/-- Every mode charging key generation inherits the 127-bit guarantee. -/
theorem xmss_sufCma_secure_127_of_keygen (mode : CountingMode) (hk : mode.keygen = true) :
    XmssSufCmaSecure mode 127 :=
  Modes.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hk]) xmss 127
    xmss_sufCma_keygen_127

/-- Charging direct queries and verification gives 127-bit security. -/
theorem xmss_sufCma_verifier_127 : XmssSufCmaSecure ⟨false, false, true, false⟩ 127 :=
  Modes.sufCmaVerifier_127

/-- info: 'XmssSecurity.xmss_sufCma_verifier_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_verifier_127

/-- Every mode charging verification inherits the 127-bit guarantee. -/
theorem xmss_sufCma_secure_127_of_verifier (mode : CountingMode) (hv : mode.verifier = true) :
    XmssSufCmaSecure mode 127 :=
  Modes.hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hv]) xmss 127
    xmss_sufCma_verifier_127

/-- The direct mode charges the least, so its level holds in every mode. -/
theorem xmss_sufCma_secure_119 (mode : CountingMode) : XmssSufCmaSecure mode 119 :=
  Modes.hasClassicalSecurityBits_of_le (m := CountingMode.direct)
    ⟨fun h => by simp [CountingMode.direct] at h, fun h => by simp [CountingMode.direct] at h,
      fun h => by simp [CountingMode.direct] at h, fun h => by simp [CountingMode.direct] at h⟩
    xmss 119 xmss_sufCma_direct_119

/-- Every mode charging key generation, the signer, and the verifier charges at least as much as
`allHashes`, so it has 127 bits. -/
theorem xmss_sufCma_secure_127 (mode : CountingMode) (hk : mode.keygen = true)
    (hs : mode.signer = true) (hv : mode.verifier = true) : XmssSufCmaSecure mode 127 :=
  Modes.hasClassicalSecurityBits_of_le (m := CountingMode.allHashes)
    ⟨fun _ => hk, fun _ => hs, fun _ => hv, fun h => by simp [CountingMode.allHashes] at h⟩
    xmss 127 xmss_sufCma_allHashes_127

/-- info: 'XmssSecurity.xmss_sufCma_secure_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_secure_127

/-- In particular, counting every hash call and every signing request. -/
theorem xmss_sufCma_everything_127 : XmssSufCmaSecure CountingMode.everything 127 :=
  xmss_sufCma_secure_127 _ rfl rfl rfl

end XmssSecurity

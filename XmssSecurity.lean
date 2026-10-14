import XmssSecurity.Statement.Claims
import XmssSecurity.Proof.Adversary.Security
import XmssSecurity.Proof.Direct.Assemble
import XmssSecurity.Proof.Direct.DecidingAssemble
import XmssSecurity.Proof.Direct.DecidingSecurity
import XmssSecurity.Proof.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.Direct.DecidingFirstLaneExpected
import XmssSecurity.Proof.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.Direct.EncodingPrehit
import XmssSecurity.Proof.Direct.LargeBudget
import XmssSecurity.Proof.Modes.Direct
import XmssSecurity.Proof.Modes.AllHashes
import XmssSecurity.Proof.Modes.Lattice
import XmssSecurity.Proof.Modes.Projection
import XmssSecurity.Proof.Modes.Exact
import XmssSecurity.Proof.Modes.Keygen
import XmssSecurity.Proof.Modes.Verifier
import XmssSecurity.Proof.Modes.SignerAccounting
import XmssSecurity.Proof.Modes.SignerTable
import XmssSecurity.Proof.Modes.SignerPrepared
import XmssSecurity.Proof.Modes.SignerReferenceBudget
import XmssSecurity.Proof.EncodingProbability
import XmssSecurity.Proof.EncodingRejectionProbability
import XmssSecurity.Proof.EncodingAcceptanceBudget
import XmssSecurity.Proof.SignerEncodingCost
import XmssSecurity.Proof.Deterministic.SignerCost
import XmssSecurity.Proof.Deterministic.SignerPhaseCost
import XmssSecurity.Proof.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.Deterministic.SignerBudgetTransfer
import XmssSecurity.Proof.Deterministic.PreparedKeygen
import XmssSecurity.Proof.SignerSuccessBudget
import XmssSecurity.Proof.Seeded.KeygenEncodingCache
import XmssSecurity.Proof.FirstLaneEncodingExpected
import XmssSecurity.Proof.FirstLaneChainExpected
import XmssSecurity.Proof.FirstLaneEncodingCache
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
import XmssSecurity.Proof.Attack.ChainMutationSeeded
import XmssSecurity.Proof.Attack.EncodingNeighbors
import XmssSecurity.Proof.Attack.NeighborSearch
import XmssSecurity.Proof.Attack.PreimageSearch
import XmssSecurity.Proof.Attack.NeighborPreimageCache
import XmssSecurity.Proof.Attack.NeighborVerification
import XmssSecurity.Proof.Attack.NeighborExperiment
import XmssSecurity.Proof.Attack.NeighborAdversary
import XmssSecurity.Proof.Attack.NeighborGame
import XmssSecurity.Proof.Attack.NeighborSeeded
import XmssSecurity.Proof.Attack.NeighborBudget
import XmssSecurity.Proof.Attack.NeighborAccounting

/-!
# Security of XMSS in the random-oracle model

The main theorems. Each proves a claim of `Statement/Claims.lean`; the statements (the scheme,
the security notion with its counting modes, and bit security) live under `Statement/`, the
proofs under `Proof/`.

The lattice of counting modes (`Proof/Modes/Lattice.lean`) spreads the proved levels to the
other modes: 122 bits holds in every mode, and 127 bits holds in every mode charging key generation
or verification.
The one-request chain-mutation attack proves that the two modes charging no honest-party
hashes have exactly 122 bits.
The neighboring-encoding attack refutes 128 bits even when every hash and signing request
is charged, completing exact 127-bit security for every mode charging key generation or verification.
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

/-- One signing request and no direct hash queries suffice to refute 123-bit security. -/
theorem xmss_sufCma_requests_attack_122 : XmssSufCmaAttack ⟨false, false, false, true⟩ 122 :=
  Attack.chainMutation_requests_attack

/-- info: 'XmssSecurity.xmss_sufCma_requests_attack_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_requests_attack_122

/-- The same attack refutes 123-bit security in the direct-only mode. -/
theorem xmss_sufCma_direct_attack_122 : XmssSufCmaDirectAttackStatement :=
  Attack.chainMutation_direct_attack

/-- info: 'XmssSecurity.xmss_sufCma_direct_attack_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_direct_attack_122

/-- Direct-only security is exactly 122 bits. -/
theorem xmss_sufCma_direct_exact_122 :
    (SUFCMA.notion CountingMode.direct).HasExactClassicalSecurityBits xmss 122 :=
  ⟨xmss_sufCma_direct_122, xmss_sufCma_direct_attack_122⟩

/-- info: 'XmssSecurity.xmss_sufCma_direct_exact_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_direct_exact_122

/-- Charging signing requests as well as direct queries still gives exactly 122 bits. -/
theorem xmss_sufCma_requests_exact_122 :
    (SUFCMA.notion ⟨false, false, false, true⟩).HasExactClassicalSecurityBits xmss 122 :=
  ⟨xmss_sufCma_secure_122 _, xmss_sufCma_requests_attack_122⟩

/-- info: 'XmssSecurity.xmss_sufCma_requests_exact_122' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_requests_exact_122

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

/-- The neighboring-encoding attack refutes 128 bits when every hash and request is charged. -/
theorem xmss_sufCma_everything_attack_127 : XmssSufCmaEverythingAttackStatement :=
  Attack.neighbor_everything_attack

/-- info: 'XmssSecurity.xmss_sufCma_everything_attack_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_everything_attack_127

/-- Every counting mode inherits the attack against 128-bit security. -/
theorem xmss_sufCma_attack_127 (mode : CountingMode) : XmssSufCmaAttack mode 127 :=
  Modes.not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) xmss 128 xmss_sufCma_everything_attack_127

/-- info: 'XmssSecurity.xmss_sufCma_attack_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_attack_127

/-- Charging key generation or verification gives exactly 127 bits. -/
theorem xmss_sufCma_exact_127_of_keygen_or_verifier (mode : CountingMode)
    (hcharged : mode.keygen = true ∨ mode.verifier = true) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss 127 := by
  refine ⟨?_, xmss_sufCma_attack_127 mode⟩
  rcases hcharged with hkeygen | hverifier
  · exact xmss_sufCma_secure_127_of_keygen mode hkeygen
  · exact xmss_sufCma_secure_127_of_verifier mode hverifier

/-- info: 'XmssSecurity.xmss_sufCma_exact_127_of_keygen_or_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_exact_127_of_keygen_or_verifier

/-- Counting every hash call gives exactly 127 bits. -/
theorem xmss_sufCma_allHashes_exact_127 :
    (SUFCMA.notion CountingMode.allHashes).HasExactClassicalSecurityBits xmss 127 :=
  ⟨xmss_sufCma_allHashes_127, xmss_sufCma_attack_127 _⟩

/-- info: 'XmssSecurity.xmss_sufCma_allHashes_exact_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_allHashes_exact_127

/-- Counting every hash call and signing request gives exactly 127 bits. -/
theorem xmss_sufCma_everything_exact_127 :
    (SUFCMA.notion CountingMode.everything).HasExactClassicalSecurityBits xmss 127 :=
  ⟨xmss_sufCma_everything_127, xmss_sufCma_everything_attack_127⟩

/-- info: 'XmssSecurity.xmss_sufCma_everything_exact_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sufCma_everything_exact_127

end XmssSecurity

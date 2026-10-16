import XmssSecurity.Proof.Modes.QueryKinds
import XmssSecurity.Statement.Scheme.Xmss
import XmssSecurity.Proof.Adversary.Security
import XmssSecurity.Proof.Direct.Assemble
import XmssSecurity.Proof.Direct.DecidingAssemble
import XmssSecurity.Proof.Direct.DecidingSecurity
import XmssSecurity.Proof.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.Direct.DecidingSecondLaneFresh
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
import XmssSecurity.Proof.Modes.SignerPhaseCounts
import XmssSecurity.Proof.Modes.SignerSourceBudget
import XmssSecurity.Proof.Direct.CountedSourceCoupling
import XmssSecurity.Proof.Modes.SignerFirstLaneCoupling
import XmssSecurity.Proof.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.FirstLaneSampleLimit
import XmssSecurity.Proof.Direct.FirstLaneBudgetEnforcement
import XmssSecurity.Proof.Modes.SignerLimitedCoupling
import XmssSecurity.Proof.Direct.LimitedPrefixSupport
import XmssSecurity.Proof.Direct.SeedGuessingExpected
import XmssSecurity.Proof.Direct.SourceClassBudget
import XmssSecurity.Proof.Deterministic.ExpectedReferenceQueries
import XmssSecurity.Proof.Modes.SignerClassBudget
import XmssSecurity.Proof.Modes.SignerSecondaryLoss
import XmssSecurity.Proof.Modes.SignerCachedLoss
import XmssSecurity.Proof.Direct.CachedEncodingCost
import XmssSecurity.Proof.Direct.LimitedAcceptanceTransfer
import XmssSecurity.Proof.Modes.SignerCachedSecurity
import XmssSecurity.Proof.Modes.SignerAcceptedFirstLane
import XmssSecurity.Proof.Modes.SignerMixedLoss
import XmssSecurity.Proof.Direct.FreshRevealedConditioning
import XmssSecurity.Proof.Direct.RevealedEncodingPrefix
import XmssSecurity.Proof.Direct.LimitedEncodingProbe
import XmssSecurity.Proof.Direct.FreshRevealedBound
import XmssSecurity.Proof.Direct.MixedEncodingProbe
import XmssSecurity.Proof.Direct.MixedEncodingProbeBound
import XmssSecurity.Proof.Direct.MixedEncodingProbability
import XmssSecurity.Proof.Direct.MixedFirstLane
import XmssSecurity.Proof.Modes.SignerSharedPrefix
import XmssSecurity.Proof.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.Direct.SourceSigningCost
import XmssSecurity.Proof.Direct.SourceTerminalRejection
import XmssSecurity.Proof.Direct.TerminalCutSoundness
import XmssSecurity.Proof.Direct.TerminalPrunedPrefix
import XmssSecurity.Proof.Direct.TerminalQuiescence
import XmssSecurity.Proof.Direct.TerminalActivityBudget
import XmssSecurity.Proof.Direct.TerminalActivityCoupling
import XmssSecurity.Proof.Direct.SourceEncodingActivity
import XmssSecurity.Proof.Direct.TerminalActivityCancellation
import XmssSecurity.Proof.Direct.TerminalActivityBound
import XmssSecurity.Proof.Direct.TerminalMixedFirstLane
import XmssSecurity.Proof.Modes.Signer
import XmssSecurity.Proof.Direct.TerminalPrunedCoupling
import XmssSecurity.Proof.Direct.TerminalAcceptedCoupling
import XmssSecurity.Proof.Direct.VerificationAcceptance
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
import XmssSecurity.Proof.FirstLaneEncodingCount
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
import XmssSecurity.Proof.Legacy.PerModeNotionsEUFCMA

/-!
# Assembly of the strong-unforgeability classification

Combines the four minimal security proofs and the two attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`. The import list above also keeps every
proof module of the development in the default build.
-/

namespace XmssSecurity.Proof

open SUFCMA

theorem sufCma_exact (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits xmss
      (if mode.keygen || mode.signer || mode.verifier then 127 else 122) :=
  Modes.exactStatement_of_basis
    ((Modes.notion_direct_hasClassicalSecurityBits_iff xmss 122).2 Direct.sufCmaDirect_122)
    Modes.sufCmaKeygen_127 Modes.sufCmaSigner_127 Modes.sufCmaVerifier_127
    Attack.chainMutation_requests_attack Attack.neighbor_everything_attack mode

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem sufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.securityGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
  rw [Modes.hasExactClassicalSecurityBits_iff Z hZ]
  have hbits : (if (Modes.modeOf Z).keygen || (Modes.modeOf Z).signer || (Modes.modeOf Z).verifier
      then 127 else 122) =
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
    simp [Modes.modeOf, or_assoc]
  rw [← hbits]
  exact sufCma_exact (Modes.modeOf Z)

end XmssSecurity.Proof

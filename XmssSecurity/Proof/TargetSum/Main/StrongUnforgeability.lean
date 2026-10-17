import XmssSecurity.Proof.Common.Modes.QueryKinds
import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Proof.TargetSum.Adversary.Security
import XmssSecurity.Proof.TargetSum.Direct.Assemble
import XmssSecurity.Proof.TargetSum.Direct.DecidingAssemble
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecurity
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneExpected
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.TargetSum.Direct.EncodingPrehit
import XmssSecurity.Proof.TargetSum.Direct.LargeBudget
import XmssSecurity.Proof.Common.Modes.Direct
import XmssSecurity.Proof.Common.Modes.AllHashes
import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.TargetSum.Modes.Projection
import XmssSecurity.Proof.TargetSum.Modes.Exact
import XmssSecurity.Proof.TargetSum.Modes.Keygen
import XmssSecurity.Proof.TargetSum.Modes.Verifier
import XmssSecurity.Proof.TargetSum.Modes.SignerAccounting
import XmssSecurity.Proof.TargetSum.Modes.SignerTable
import XmssSecurity.Proof.TargetSum.Modes.SignerPrepared
import XmssSecurity.Proof.TargetSum.Modes.SignerReferenceBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerPhaseCounts
import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.CountedSourceCoupling
import XmssSecurity.Proof.TargetSum.Modes.SignerFirstLaneCoupling
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.TargetSum.FirstLaneSampleLimit
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneBudgetEnforcement
import XmssSecurity.Proof.TargetSum.Modes.SignerLimitedCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixSupport
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected
import XmssSecurity.Proof.TargetSum.Direct.SourceClassBudget
import XmssSecurity.Proof.TargetSum.Deterministic.ExpectedReferenceQueries
import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerSecondaryLoss
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedLoss
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceTransfer
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedSecurity
import XmssSecurity.Proof.TargetSum.Modes.SignerAcceptedFirstLane
import XmssSecurity.Proof.TargetSum.Modes.SignerMixedLoss
import XmssSecurity.Proof.TargetSum.Direct.FreshRevealedConditioning
import XmssSecurity.Proof.TargetSum.Direct.RevealedEncodingPrefix
import XmssSecurity.Proof.TargetSum.Direct.LimitedEncodingProbe
import XmssSecurity.Proof.TargetSum.Direct.FreshRevealedBound
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbe
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbeBound
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbability
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane
import XmssSecurity.Proof.TargetSum.Modes.SignerSharedPrefix
import XmssSecurity.Proof.TargetSum.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.TargetSum.Direct.SourceSigningCost
import XmssSecurity.Proof.TargetSum.Direct.SourceTerminalRejection
import XmssSecurity.Proof.TargetSum.Direct.TerminalCutSoundness
import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix
import XmssSecurity.Proof.TargetSum.Direct.TerminalQuiescence
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityBudget
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCoupling
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingActivity
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCancellation
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityBound
import XmssSecurity.Proof.TargetSum.Direct.TerminalMixedFirstLane
import XmssSecurity.Proof.TargetSum.Modes.Signer
import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedCoupling
import XmssSecurity.Proof.TargetSum.Direct.TerminalAcceptedCoupling
import XmssSecurity.Proof.TargetSum.Direct.VerificationAcceptance
import XmssSecurity.Proof.TargetSum.EncodingProbability
import XmssSecurity.Proof.TargetSum.EncodingRejectionProbability
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.SignerEncodingCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerBudgetTransfer
import XmssSecurity.Proof.TargetSum.Deterministic.PreparedKeygen
import XmssSecurity.Proof.TargetSum.SignerSuccessBudget
import XmssSecurity.Proof.TargetSum.Seeded.KeygenEncodingCache
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingExpected
import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCache
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCount
import XmssSecurity.Proof.TargetSum.FreshPathProbability
import XmssSecurity.Proof.TargetSum.Attack.PathBounds
import XmssSecurity.Proof.TargetSum.Attack.ChainMutation
import XmssSecurity.Proof.TargetSum.Attack.ChainMutationAccounting
import XmssSecurity.Proof.TargetSum.Attack.MutationPath
import XmssSecurity.Proof.TargetSum.Attack.MutationProbability
import XmssSecurity.Proof.TargetSum.Attack.MutationSigningCache
import XmssSecurity.Proof.TargetSum.Attack.MutationVerification
import XmssSecurity.Proof.TargetSum.Attack.MutationAverage
import XmssSecurity.Proof.TargetSum.Attack.MutationGame
import XmssSecurity.Proof.TargetSum.Attack.ChainMutationSeeded
import XmssSecurity.Proof.TargetSum.Attack.EncodingNeighbors
import XmssSecurity.Proof.TargetSum.Attack.NeighborSearch
import XmssSecurity.Proof.TargetSum.Attack.PreimageSearch
import XmssSecurity.Proof.TargetSum.Attack.NeighborPreimageCache
import XmssSecurity.Proof.TargetSum.Attack.NeighborVerification
import XmssSecurity.Proof.TargetSum.Attack.NeighborExperiment
import XmssSecurity.Proof.TargetSum.Attack.NeighborAdversary
import XmssSecurity.Proof.TargetSum.Attack.NeighborGame
import XmssSecurity.Proof.TargetSum.Attack.NeighborSeeded
import XmssSecurity.Proof.TargetSum.Attack.NeighborBudget
import XmssSecurity.Proof.TargetSum.Attack.NeighborAccounting
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# Assembly of the strong-unforgeability classification

Combines the four minimal security proofs and the two attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`. The import list above also keeps every
proof module of the development in the default build.
-/

namespace XmssSecurity.TargetSum.Proof

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
theorem lossySufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.lossyGame).HasExactClassicalSecurityBits xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
  rw [Modes.hasExactClassicalSecurityBits_iff Z hZ]
  have hbits : (if (Modes.modeOf Z).keygen || (Modes.modeOf Z).signer || (Modes.modeOf Z).verifier
      then 127 else 122) =
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
    simp [Modes.modeOf, or_assoc]
  rw [← hbits]
  exact sufCma_exact (Modes.modeOf Z)

end XmssSecurity.TargetSum.Proof

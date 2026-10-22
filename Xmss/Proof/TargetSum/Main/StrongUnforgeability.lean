import Xmss.Proof.Common.Modes.QueryKinds
import Xmss.Proof.Generic.Scheme.Xmss
import Xmss.Proof.Generic.Adversary.Embedding
import Xmss.Proof.Generic.Seeded.BudgetTransfer
import Xmss.Proof.Generic.CappedExactFirstLaneBound
import Xmss.Proof.Generic.Direct.DecidingFirstLane
import Xmss.Proof.Generic.Direct.Bridge
import Xmss.Proof.Generic.Direct.SeedGuessing
import Xmss.Proof.TargetSum.Direct.DecidingSecurity
import Xmss.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import Xmss.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import Xmss.Proof.TargetSum.Direct.DecidingFirstLaneExpected
import Xmss.Proof.TargetSum.Direct.DecidingAcceptedProbe
import Xmss.Proof.Generic.Direct.EncodingPrehit
import Xmss.Proof.Common.Modes.Direct
import Xmss.Proof.Common.Modes.AllHashes
import Xmss.Proof.Common.Modes.Lattice
import Xmss.Proof.Generic.Modes.Projection
import Xmss.Proof.Generic.Modes.Exact
import Xmss.Proof.TargetSum.Modes.Keygen
import Xmss.Proof.TargetSum.Modes.Verifier
import Xmss.Proof.TargetSum.Modes.SignerAccounting
import Xmss.Proof.TargetSum.Modes.SignerTable
import Xmss.Proof.TargetSum.Modes.SignerPrepared
import Xmss.Proof.TargetSum.Modes.SignerReferenceBudget
import Xmss.Proof.TargetSum.Modes.SignerPhaseCounts
import Xmss.Proof.TargetSum.Modes.SignerSourceBudget
import Xmss.Proof.TargetSum.Direct.CountedSourceCoupling
import Xmss.Proof.TargetSum.Direct.FirstLaneSampleBudget
import Xmss.Proof.TargetSum.Direct.FirstLaneStepBudget
import Xmss.Proof.TargetSum.FirstLaneSampleLimit
import Xmss.Proof.TargetSum.Direct.FirstLaneBudgetEnforcement
import Xmss.Proof.TargetSum.Direct.LimitedPrefixCoupling
import Xmss.Proof.TargetSum.Direct.LimitedAcceptedProbe
import Xmss.Proof.TargetSum.Direct.LimitedPrefixSupport
import Xmss.Proof.TargetSum.Direct.SeedGuessingExpected
import Xmss.Proof.TargetSum.Direct.SourceClassBudget
import Xmss.Proof.TargetSum.Deterministic.ExpectedReferenceQueries
import Xmss.Proof.TargetSum.Modes.SignerClassBudget
import Xmss.Proof.TargetSum.Direct.SourceLossBudget
import Xmss.Proof.TargetSum.Direct.CachedEncodingCost
import Xmss.Proof.TargetSum.Direct.SourcePrefixAcceptance
import Xmss.Proof.TargetSum.Modes.SignerCachedSecurity
import Xmss.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import Xmss.Proof.TargetSum.Direct.FreshVerificationProbability
import Xmss.Proof.TargetSum.Direct.FreshRevealedConditioning
import Xmss.Proof.TargetSum.Direct.RevealedEncodingPrefix
import Xmss.Proof.TargetSum.Direct.LimitedEncodingProbe
import Xmss.Proof.TargetSum.Direct.MixedEncodingProbe
import Xmss.Proof.TargetSum.Direct.MixedEncodingProbeBound
import Xmss.Proof.TargetSum.Direct.MixedEncodingProbability
import Xmss.Proof.TargetSum.Direct.MixedFirstLane
import Xmss.Proof.TargetSum.Modes.SignerSharedPrefix
import Xmss.Proof.TargetSum.Direct.SourceBudgetExhaustion
import Xmss.Proof.TargetSum.Direct.SourceSigningCost
import Xmss.Proof.TargetSum.Direct.TerminalCutSoundness
import Xmss.Proof.TargetSum.Direct.TerminalPrunedPrefix
import Xmss.Proof.TargetSum.Direct.TerminalActivityBudget
import Xmss.Proof.TargetSum.Direct.TerminalActivityCoupling
import Xmss.Proof.TargetSum.Direct.SourceEncodingActivity
import Xmss.Proof.TargetSum.Direct.TerminalActivityCancellation
import Xmss.Proof.TargetSum.Direct.TerminalActivityBound
import Xmss.Proof.TargetSum.Direct.TerminalMixedFirstLane
import Xmss.Proof.TargetSum.Modes.Signer
import Xmss.Proof.TargetSum.Direct.TerminalAcceptedCoupling
import Xmss.Proof.TargetSum.Direct.VerificationAcceptance
import Xmss.Proof.TargetSum.EncodingProbability
import Xmss.Proof.Generic.EncodingRejectionProbability
import Xmss.Proof.TargetSum.EncodingAcceptanceBudget
import Xmss.Proof.TargetSum.SignerEncodingCost
import Xmss.Proof.TargetSum.Deterministic.SignerCost
import Xmss.Proof.TargetSum.Deterministic.SignerPhaseCost
import Xmss.Proof.TargetSum.Deterministic.SignerReferenceCost
import Xmss.Proof.TargetSum.Deterministic.SignerBudgetTransfer
import Xmss.Proof.TargetSum.Deterministic.PreparedKeygen
import Xmss.Proof.Generic.Seeded.KeygenExpansion
import Xmss.Proof.TargetSum.FirstLaneEncodingExpected
import Xmss.Proof.TargetSum.FirstLaneChainExpected
import Xmss.Proof.TargetSum.FirstLaneEncodingCache
import Xmss.Proof.TargetSum.FirstLaneEncodingCount
import Xmss.Proof.Generic.FreshPathProbability
import Xmss.Proof.Generic.Attack.PathBounds
import Xmss.Proof.Generic.Attack.ChainMutation
import Xmss.Proof.Generic.Attack.ChainMutationAccounting
import Xmss.Proof.Generic.Attack.MutationPath
import Xmss.Proof.Generic.Attack.MutationPathCache
import Xmss.Proof.Generic.Attack.MutationSigningCache
import Xmss.Proof.Generic.Attack.MutationVerification
import Xmss.Proof.TargetSum.Attack.MutationAverage
import Xmss.Proof.TargetSum.Attack.MutationGame
import Xmss.Proof.TargetSum.Attack.ChainMutationSeeded
import Xmss.Proof.TargetSum.Attack.EncodingNeighbors
import Xmss.Proof.TargetSum.Attack.NeighborSearch
import Xmss.Proof.TargetSum.Attack.PreimageSearch
import Xmss.Proof.TargetSum.Attack.NeighborPreimageCache
import Xmss.Proof.TargetSum.Attack.NeighborVerification
import Xmss.Proof.TargetSum.Attack.NeighborExperiment
import Xmss.Proof.TargetSum.Attack.NeighborAdversary
import Xmss.Proof.TargetSum.Attack.NeighborGame
import Xmss.Proof.TargetSum.Attack.NeighborSeeded
import Xmss.Proof.TargetSum.Attack.NeighborBudget
import Xmss.Proof.TargetSum.Attack.NeighborAccounting
import Xmss.Proof.Common.Legacy.PerModeNotionsEUFCMA
import Xmss.Proof.TargetSum.Code

/-!
# Assembly of the strong-unforgeability classification

Combines the four minimal security proofs and the two attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`. The import list above also keeps every
proof module of the development in the default build.
-/

open Xmss.Generic

namespace Xmss.TargetSum

open Unforgeability SUFCMA

theorem sufCma_exact (mode : CountingMode) :
    (SUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss
      (if mode.keygen || mode.signer || mode.verifier then 127 else 122) :=
  Modes.exactStatement_of_basis
    ((Modes.notion_direct_hasClassicalSecurityBits_iff Generic.xmss 122).2 Direct.sufCmaDirect_122)
    Modes.sufCmaKeygen_127 Modes.sufCmaSigner_127 Modes.sufCmaVerifier_127
    Attack.chainMutation_requests_attack Attack.neighbor_everything_attack mode

/-- The classification for counting modes given as sets of query kinds containing the adversary's
own hash queries. -/
theorem lossySufCma_exact_of_hash_mem (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) :
    (SUFCMA.lossyGame).HasExactClassicalSecurityBits Generic.xmss Z
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
  rw [Modes.hasExactClassicalSecurityBits_iff Z hZ]
  have hbits : (if (Modes.modeOf Z).keygen || (Modes.modeOf Z).signer || (Modes.modeOf Z).verifier
      then 127 else 122) =
      (if QueryKind.keygen ∈ Z ∨ QueryKind.signer ∈ Z ∨ QueryKind.verifier ∈ Z then 127 else 122) := by
    simp [Modes.modeOf, or_assoc]
  rw [← hbits]
  exact sufCma_exact (Modes.modeOf Z)

end Xmss.TargetSum

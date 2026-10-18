import XmssSecurity.Proof.Common.Modes.QueryKinds
import XmssSecurity.Proof.Generic.Scheme.Xmss
import XmssSecurity.Proof.Generic.Adversary.Embedding
import XmssSecurity.Proof.Generic.Seeded.BudgetTransfer
import XmssSecurity.Proof.Generic.CappedExactFirstLaneBound
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLane
import XmssSecurity.Proof.Generic.Direct.Bridge
import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecurity
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneAccepted
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneExpected
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.Generic.Direct.EncodingPrehit
import XmssSecurity.Proof.Common.Modes.Direct
import XmssSecurity.Proof.Common.Modes.AllHashes
import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Generic.Modes.Projection
import XmssSecurity.Proof.Generic.Modes.Exact
import XmssSecurity.Proof.TargetSum.Modes.Keygen
import XmssSecurity.Proof.TargetSum.Modes.Verifier
import XmssSecurity.Proof.TargetSum.Modes.SignerAccounting
import XmssSecurity.Proof.TargetSum.Modes.SignerTable
import XmssSecurity.Proof.TargetSum.Modes.SignerPrepared
import XmssSecurity.Proof.TargetSum.Modes.SignerReferenceBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerPhaseCounts
import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.CountedSourceCoupling
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSampleBudget
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.TargetSum.FirstLaneSampleLimit
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneBudgetEnforcement
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixSupport
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected
import XmssSecurity.Proof.TargetSum.Direct.SourceClassBudget
import XmssSecurity.Proof.TargetSum.Deterministic.ExpectedReferenceQueries
import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Direct.SourcePrefixAcceptance
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedSecurity
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.Direct.FreshRevealedConditioning
import XmssSecurity.Proof.TargetSum.Direct.RevealedEncodingPrefix
import XmssSecurity.Proof.TargetSum.Direct.LimitedEncodingProbe
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbe
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbeBound
import XmssSecurity.Proof.TargetSum.Direct.MixedEncodingProbability
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane
import XmssSecurity.Proof.TargetSum.Modes.SignerSharedPrefix
import XmssSecurity.Proof.TargetSum.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.TargetSum.Direct.SourceSigningCost
import XmssSecurity.Proof.TargetSum.Direct.TerminalCutSoundness
import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityBudget
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCoupling
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingActivity
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCancellation
import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityBound
import XmssSecurity.Proof.TargetSum.Direct.TerminalMixedFirstLane
import XmssSecurity.Proof.TargetSum.Modes.Signer
import XmssSecurity.Proof.TargetSum.Direct.TerminalAcceptedCoupling
import XmssSecurity.Proof.TargetSum.Direct.VerificationAcceptance
import XmssSecurity.Proof.TargetSum.EncodingProbability
import XmssSecurity.Proof.Generic.EncodingRejectionProbability
import XmssSecurity.Proof.TargetSum.EncodingAcceptanceBudget
import XmssSecurity.Proof.TargetSum.SignerEncodingCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerPhaseCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerReferenceCost
import XmssSecurity.Proof.TargetSum.Deterministic.SignerBudgetTransfer
import XmssSecurity.Proof.TargetSum.Deterministic.PreparedKeygen
import XmssSecurity.Proof.Generic.Seeded.KeygenExpansion
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingExpected
import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCache
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCount
import XmssSecurity.Proof.Generic.FreshPathProbability
import XmssSecurity.Proof.Generic.Attack.PathBounds
import XmssSecurity.Proof.Generic.Attack.ChainMutation
import XmssSecurity.Proof.Generic.Attack.ChainMutationAccounting
import XmssSecurity.Proof.Generic.Attack.MutationPath
import XmssSecurity.Proof.Generic.Attack.MutationPathCache
import XmssSecurity.Proof.Generic.Attack.MutationSigningCache
import XmssSecurity.Proof.Generic.Attack.MutationVerification
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
import XmssSecurity.Proof.TargetSum.Code

/-!
# Assembly of the strong-unforgeability classification

Combines the four minimal security proofs and the two attacks into the exact classification
stated in `Statement/StrongUnforgeabilityTheorems.lean`. The import list above also keeps every
proof module of the development in the default build.
-/

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Proof

open SUFCMA

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

end XmssSecurity.TargetSum.Proof

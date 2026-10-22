import SlhDsaSecurity.Proof.VerifierFormat
import SlhDsaSecurity.Proof.RandomiserCharge
import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.ReplayGate
import SlhDsaSecurity.Proof.KeygenBudget
import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.RoutedSplit
import SlhDsaSecurity.Proof.WalkDefects
import SlhDsaSecurity.Proof.CanonicalSplit
import SlhDsaSecurity.Proof.WriterState
import SlhDsaSecurity.Proof.ClassExpectation
import SlhDsaSecurity.Proof.RandomizerGate
import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.SensitiveExpectation
import SlhDsaSecurity.Proof.CacheAvailability
import SlhDsaSecurity.Proof.SplitRouted
import SlhDsaSecurity.Proof.CoverageRouted
import SlhDsaSecurity.Proof.CanonicalSignature
import SlhDsaSecurity.Proof.SensitiveWarm
import SlhDsaSecurity.Proof.LazyBudget
import SlhDsaSecurity.Proof.WarmProbes
import SlhDsaSecurity.Proof.ClaimedProbes
import SlhDsaSecurity.Proof.ChargedProbe
import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.AddressBounds
import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.StalledRun
import SlhDsaSecurity.Proof.HonestMessage
import SlhDsaSecurity.Proof.DrawnTable
import SlhDsaSecurity.Proof.TableBlind
import SlhDsaSecurity.Proof.RecordedBudget
import SlhDsaSecurity.Proof.HonestGrowth
import SlhDsaSecurity.Proof.GraphStakes
import SlhDsaSecurity.Proof.RecordedQueries
import SlhDsaSecurity.Proof.SensitiveQuery
import SlhDsaSecurity.Proof.LazyBridge
import SlhDsaSecurity.Proof.AdversaryQueries
import SlhDsaSecurity.Proof.SensitiveShape
import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.WotsResidueReduction
import SlhDsaSecurity.Proof.DigestTape
import SlhDsaSecurity.Proof.SplitCharged
import SlhDsaSecurity.Proof.StripCached
import SlhDsaSecurity.Proof.VerifierProbes
import SlhDsaSecurity.Proof.HonestProbes
import SlhDsaSecurity.Proof.FaultCharge
import SlhDsaSecurity.Proof.ForsBranch
import SlhDsaSecurity.Proof.WarmedSplit
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.CachedRun
import SlhDsaSecurity.Proof.Parameters
import SlhDsaSecurity.Proof.Checksum
import SlhDsaSecurity.Proof.ForsCoverage
import SlhDsaSecurity.Proof.ForsMoments
import SlhDsaSecurity.Proof.ForsConcentration
import SlhDsaSecurity.Proof.Hashing
import SlhDsaSecurity.Proof.HashSeparation
import SlhDsaSecurity.Proof.Security
import SlhDsaSecurity.Proof.SignatureCanonical
import SlhDsaSecurity.Proof.PartialDigest
import SlhDsaSecurity.Proof.ForsConcentrationOccupancy
import SlhDsaSecurity.Proof.VerificationQueries
import SlhDsaSecurity.Proof.KeygenUniform
import SlhDsaSecurity.Proof.VerificationBudget
import SlhDsaSecurity.Proof.ChecksumAntichain
import SlhDsaSecurity.Proof.ForsAdaptiveTargets
import SlhDsaSecurity.Proof.FramingOverlap
import SlhDsaSecurity.Proof.Correctness.Scheme
import SlhDsaSecurity.Proof.ForsPrefixCapacity
import SlhDsaSecurity.Proof.ForsConcentrationExtended
import SlhDsaSecurity.Proof.Correctness.SharedROM
import SlhDsaSecurity.Proof.BlindKey
import SlhDsaSecurity.Proof.ForsDisclosureTape
import SlhDsaSecurity.Proof.ForsDisclosurePrefix
import SlhDsaSecurity.Proof.ForsLeaveOneOut
import SlhDsaSecurity.Proof.ForsConcentrationSharper
import SlhDsaSecurity.Proof.ROMPresampling
import SlhDsaSecurity.Proof.CanonicalGraph.Correspondence
import SlhDsaSecurity.Proof.CanonicalGraph.Parsing
import SlhDsaSecurity.Proof.CanonicalGraph.Separation
import SlhDsaSecurity.Proof.CanonicalGraph.Programming
import SlhDsaSecurity.Proof.Extraction.Merkle
import SlhDsaSecurity.Proof.Extraction.Wots
import SlhDsaSecurity.Proof.Extraction.Fors
import SlhDsaSecurity.Proof.Extraction.Hypertree
import SlhDsaSecurity.Proof.Extraction.WotsPreimage
import SlhDsaSecurity.Proof.Extraction.HypertreeChain
import SlhDsaSecurity.Proof.CollisionCharge
import SlhDsaSecurity.Proof.FreshHitBound
import SlhDsaSecurity.Proof.FramingLeak
import SlhDsaSecurity.Proof.CanonicalTarget
import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.StructuralTerm
import SlhDsaSecurity.Proof.FreshDigest
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.WholeGameStructural
import SlhDsaSecurity.Proof.ForsCoverageTerm
import SlhDsaSecurity.Proof.Assembly
import SlhDsaSecurity.Proof.PerQueryBudget
import SlhDsaSecurity.Proof.CombinedCharge
import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.ClassCharge
import SlhDsaSecurity.Proof.SeedDeferral
import SlhDsaSecurity.Proof.QueryCached
import SlhDsaSecurity.Proof.ClassBudget
import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.MerkleCharge
import SlhDsaSecurity.Proof.ForsCharge
import SlhDsaSecurity.Proof.WotsCharge
import SlhDsaSecurity.Proof.ForsLeafCharge
import SlhDsaSecurity.Proof.CanonicalCells
import SlhDsaSecurity.Proof.PathEntry
import SlhDsaSecurity.Proof.WotsEntry
import SlhDsaSecurity.Proof.HypertreeDispatch
import SlhDsaSecurity.Proof.InputCoupling
import SlhDsaSecurity.Proof.ForsDispatch
import SlhDsaSecurity.Proof.BlindComparison
import SlhDsaSecurity.Proof.TrackedQueries
import SlhDsaSecurity.Proof.WeightedCharge
import SlhDsaSecurity.Proof.Presample
import SlhDsaSecurity.Proof.GameBridge
import SlhDsaSecurity.Proof.MainTheorem
import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.DigestInputDistinct
import SlhDsaSecurity.Proof.FramingClosure
import SlhDsaSecurity.Proof.SharedOracleArithmetic
import SlhDsaSecurity.Proof.EligibilityCertificate.Coefficients
import SlhDsaSecurity.Proof.KeygenValue
import SlhDsaSecurity.Proof.RecordedPhase
import SlhDsaSecurity.Proof.LinkedGame
import SlhDsaSecurity.Proof.CanonicalGraph.Children
import SlhDsaSecurity.Proof.CanonicalGraph.Nodes
import SlhDsaSecurity.Proof.CanonicalGraph.Address
import SlhDsaSecurity.Proof.CanonicalGraph.Input
import SlhDsaSecurity.Proof.CanonicalGraph.Evaluation
import SlhDsaSecurity.Proof.Correctness.Hypertree
import SlhDsaSecurity.Proof.Correctness.Merkle
import SlhDsaSecurity.Proof.Correctness.Naturality
import SlhDsaSecurity.Proof.Correctness.Wots
import SlhDsaSecurity.Proof.Correctness.BinaryPath
import SlhDsaSecurity.Proof.EligibilityCertificate.Arithmetic
import SlhDsaSecurity.Proof.Extraction.BinaryPath
import SlhDsaSecurity.Proof.ForsConcentrationPoisson
import SlhDsaSecurity.Proof.Signature
import SlhDsaSecurity.Proof.GraphFreshSampling
import SlhDsaSecurity.Proof.KeygenFresh
import SlhDsaSecurity.Proof.MessageDigest
import SlhDsaSecurity.Proof.VerifierNaturality
import SlhDsaSecurity.Proof.AnswerSide
import SlhDsaSecurity.Proof.SigningFaithful
import SlhDsaSecurity.Proof.BlockDisclosures
import SlhDsaSecurity.Proof.SplitPrefix
import SlhDsaSecurity.Proof.RandomiserProvenance
import SlhDsaSecurity.Proof.PhaseProvenance
import SlhDsaSecurity.Proof.CacheProvenance
import SlhDsaSecurity.Proof.SplitWitness
import SlhDsaSecurity.Proof.RandomiserDeferral
import SlhDsaSecurity.Proof.RecordedTail
import SlhDsaSecurity.Proof.LateCharge
import SlhDsaSecurity.Proof.TapeFactor
import SlhDsaSecurity.Proof.PotentialCharge
import SlhDsaSecurity.Proof.WalkTable
import SlhDsaSecurity.Proof.LateRate
import SlhDsaSecurity.Proof.TableTail
import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.SharedJoin

/-- info: 'SlhDsaSecurity.parameters_consistent' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.parameters_consistent

/-- info: 'SlhDsaSecurity.Checksum.checksum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.checksum_le

/-- info: 'SlhDsaSecurity.Checksum.chainVerificationCalls_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.chainVerificationCalls_eq

/-- info: 'SlhDsaSecurity.Checksum.chainVerificationCalls_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.chainVerificationCalls_bounds

/-- info: 'SlhDsaSecurity.Checksum.chainVerificationCalls_extremes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.chainVerificationCalls_extremes

/-- info: 'SlhDsaSecurity.ForsCoverage.covered_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverage.covered_card

/-- info: 'SlhDsaSecurity.ForsCoverage.fresh_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverage.fresh_coverage

/-- info: 'SlhDsaSecurity.ForsCoverage.fresh_coverage_le_of_loads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverage.fresh_coverage_le_of_loads

/-- info: 'SlhDsaSecurity.ForsMoments.stirlingRow_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsMoments.stirlingRow_getD

/-- info: 'SlhDsaSecurity.ForsMoments.touchard_eq_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsMoments.touchard_eq_cached

/-- info: 'SlhDsaSecurity.ForsMoments.touchard_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsMoments.touchard_bounds

/-- info: 'SlhDsaSecurity.ForsMoments.sixth_moment_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsMoments.sixth_moment_scalar

/-- info: 'SlhDsaSecurity.bytesBE_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.bytesBE_injective

/-- info: 'SlhDsaSecurity.Address.toBytes_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Address.toBytes_injective

/-- info: 'SlhDsaSecurity.Hashing.tweakableInput_ne_of_type_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Hashing.tweakableInput_ne_of_type_ne

/-- info: 'SlhDsaSecurity.Hashing.randomizerInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Hashing.randomizerInput_injective

/-- info: 'SlhDsaSecurity.Hashing.messageInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Hashing.messageInput_injective

/-- info: 'SlhDsaSecurity.Hashing.message_randomizer_overlap' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Hashing.message_randomizer_overlap

/-- info: 'SlhDsaSecurity.Message.frame_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Message.frame_injective

/-- info: 'SlhDsaSecurity.MessageDigest.split_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MessageDigest.split_bijective

/-- info: 'SlhDsaSecurity.MessageDigest.evalDist_parse_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MessageDigest.evalDist_parse_uniform

/-- info: 'SlhDsaSecurity.ForsCoverage.fresh_digest_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverage.fresh_digest_coverage

/-- info: 'SlhDsaSecurity.HashSeparation.message_tweakable_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.message_tweakable_ne

/-- info: 'SlhDsaSecurity.HashSeparation.randomizer_tweakable_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.randomizer_tweakable_ne

/-- info: 'SlhDsaSecurity.HashSeparation.prob_possible_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.prob_possible_le

/-- info: 'SlhDsaSecurity.Security.experiment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.experiment

/-- info: 'SlhDsaSecurity.Security.strong_implies_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.strong_implies_standard

/-- info: 'SlhDsaSecurity.ForsConcentration.poisson_integral_power_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_integral_power_nat

/-- info: 'SlhDsaSecurity.ForsConcentration.centeredMoment_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.centeredMoment_bounds

/-- info: 'SlhDsaSecurity.ForsConcentration.independent_sum_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.independent_sum_moments

/-- info: 'SlhDsaSecurity.ForsConcentration.poisson_load_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_load_tail

/-- info: 'SlhDsaSecurity.Signature.fromBytes_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.fromBytes_toBytes

/-- info: 'SlhDsaSecurity.Signature.toBytes_fromBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.toBytes_fromBytes

/-- info: 'SlhDsaSecurity.PartialDigest.coverage_le_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.coverage_le_256

/-- info: 'SlhDsaSecurity.ForsConcentration.uniform_load_tail_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniform_load_tail_of_le

/-- info: 'SlhDsaSecurity.VerificationQueries.verifyInternal_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.verifyInternal_bounds

/-- info: 'SlhDsaSecurity.VerificationQueries.verifyInternal_simulated_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.verifyInternal_simulated_bounds

/-- info: 'SlhDsaSecurity.KeygenUniform.publicPair_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.publicPair_uniform

/-- info: 'SlhDsaSecurity.KeygenUniform.keygen_prob_possible_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.keygen_prob_possible_le

/-- info: 'SlhDsaSecurity.VerificationBudget.accepted_outcome_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.accepted_outcome_work

/-- info: 'SlhDsaSecurity.VerificationBudget.advantage_eq_zero_of_small_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.advantage_eq_zero_of_small_budget

/-- info: 'SlhDsaSecurity.Checksum.exists_decreased_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.exists_decreased_digit

/-- info: 'SlhDsaSecurity.ForsAdaptiveTargets.coverage_mixture_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.coverage_mixture_le

/-- info: 'SlhDsaSecurity.FramingOverlap.keygen_zero_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.keygen_zero_probability

/-- info: 'SlhDsaSecurity.Correctness.Scheme.verify_sign_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Scheme.verify_sign_keygen

/-- info: 'SlhDsaSecurity.Correctness.Fors.publicKeyFromSignature_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Fors.publicKeyFromSignature_sign

/-- info: 'SlhDsaSecurity.ForsPrefixCapacity.simultaneous_prefix_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.simultaneous_prefix_cap

/-- info: 'SlhDsaSecurity.Correctness.SharedROM.experiment_probability_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.experiment_probability_one

/-- info: 'SlhDsaSecurity.BlindKey.mixture_hit_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindKey.mixture_hit_le_expected

/-- info: 'SlhDsaSecurity.ForsDisclosureTape.bad_load_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.bad_load_probability

/-- info: 'SlhDsaSecurity.ForsDisclosurePrefix.bad_prefix_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.bad_prefix_probability

/-- info: 'SlhDsaSecurity.ForsLeaveOneOut.independent_tape_mixture_coverage_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.independent_tape_mixture_coverage_le

/-- info: 'SlhDsaSecurity.ForsLeaveOneOut.independent_tape_coverage_le_sharper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.independent_tape_coverage_le_sharper

/-- info: 'SlhDsaSecurity.ROMPresampling.evalDist_security_after_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.evalDist_security_after_preparation

/-- info: 'SlhDsaSecurity.ROMPresampling.security_budget_after_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.security_budget_after_preparation

/-- info: 'SlhDsaSecurity.CanonicalGraph.value_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.value_unique

/-- info: 'SlhDsaSecurity.CanonicalGraph.wots_sign_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.wots_sign_cells

/-- info: 'SlhDsaSecurity.CanonicalGraph.fors_publicKey_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.fors_publicKey_cell

/-- info: 'SlhDsaSecurity.CanonicalGraph.blindProbe_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.blindProbe_canonical

/-- info: 'SlhDsaSecurity.CanonicalGraph.StructuralNode.address_withinBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.StructuralNode.address_withinBounds

/-- info: 'SlhDsaSecurity.CanonicalGraph.Programming.warmup_seed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.warmup_seed_uniform

/-- info: 'SlhDsaSecurity.Extraction.BinaryPath.canonical_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.canonical_or_collision

/-- info: 'SlhDsaSecurity.Extraction.Merkle.root_eq_canonical_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Merkle.root_eq_canonical_or_collision

/-- info: 'SlhDsaSecurity.Extraction.Wots.publicKey_eq_canonical_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Wots.publicKey_eq_canonical_or_collision

/-- info: 'SlhDsaSecurity.FramingClosure.chainFrame_family_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_family_injective

/-- info: 'SlhDsaSecurity.FramingClosure.prepend_digest_exists_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.prepend_digest_exists_frame

/-- info: 'SlhDsaSecurity.SharedOracleArithmetic.proposed_bound_exceeds_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.proposed_bound_exceeds_target

/-- info: 'SlhDsaSecurity.EligibilityCertificate.count_gt' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.count_gt

/-- info: 'SlhDsaSecurity.EligibilityCertificate.coeff_eq_digit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.coeff_eq_digit

/-- info: 'SlhDsaSecurity.Extraction.Fors.root_eq_canonical_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Fors.root_eq_canonical_or_collision

/-- info: 'SlhDsaSecurity.Extraction.Fors.publicKey_eq_canonical_roots_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Fors.publicKey_eq_canonical_roots_or_collision

/-- info: 'SlhDsaSecurity.Extraction.Hypertree.layer_canonical_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Hypertree.layer_canonical_or_collision

/-- info: 'SlhDsaSecurity.Extraction.WotsPreimage.exists_preimage_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.WotsPreimage.exists_preimage_witness

/-- info: 'SlhDsaSecurity.Extraction.HypertreeChain.rootFromSignature_fault_or_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.rootFromSignature_fault_or_canonical

/-- info: 'SlhDsaSecurity.Extraction.HypertreeChain.verify_fault_or_fors_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.verify_fault_or_fors_canonical

/-- info: 'SlhDsaSecurity.Extraction.Fors.publicKey_canonical_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Fors.publicKey_canonical_decomposition

/-- info: 'SlhDsaSecurity.Extraction.Fors.recoveredLeaf_canonical_secret_or_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Fors.recoveredLeaf_canonical_secret_or_collision

/-- info: 'SlhDsaSecurity.CollisionCharge.fresh_tweakable_prob_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionCharge.fresh_tweakable_prob_hit

/-- info: 'SlhDsaSecurity.CollisionCharge.fresh_tweakable_prob_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionCharge.fresh_tweakable_prob_mem_le

/-- info: 'SlhDsaSecurity.FreshHitBound.prob_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshHitBound.prob_hit_le

/-- info: 'SlhDsaSecurity.FreshHitBound.prob_hit_const_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshHitBound.prob_hit_const_le

/-- info: 'SlhDsaSecurity.FramingLeak.randomizer_eq_truncate_messageDigest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.randomizer_eq_truncate_messageDigest

/-- info: 'SlhDsaSecurity.FramingLeak.exists_legal_request_leaking_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.exists_legal_request_leaking_digest

/-- info: 'SlhDsaSecurity.CanonicalTarget.canonicalTarget_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalTarget.canonicalTarget_canonical

/-- info: 'SlhDsaSecurity.CanonicalTarget.clean_of_canonical_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalTarget.clean_of_canonical_cache

/-- info: 'SlhDsaSecurity.CanonicalTarget.hit_of_deviating_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalTarget.hit_of_deviating_collision

/-- info: 'SlhDsaSecurity.GrowthCharge.cache_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.cache_mono

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_hitWithin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_hitWithin_le

/-- info: 'SlhDsaSecurity.StructuralTerm.prob_deviatingCollision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StructuralTerm.prob_deviatingCollision_le

/-- info: 'SlhDsaSecurity.FreshDigest.fresh_messageDigest_parse_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.fresh_messageDigest_parse_uniform

/-- info: 'SlhDsaSecurity.FreshDigest.fresh_randomizer_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.fresh_randomizer_uniform

/-- info: 'SlhDsaSecurity.Security.totalAdvantage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.totalAdvantage_eq

/-- info: 'SlhDsaSecurity.Security.total_strong_implies_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.total_strong_implies_standard

/-- info: 'SlhDsaSecurity.GrowthBudget.growth_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.growth_le_count

/-- info: 'SlhDsaSecurity.WholeGameStructural.prob_deviatingCollision_whole_game_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.prob_deviatingCollision_whole_game_le

/-- info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_bind

/-- info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_eq_component' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_eq_component

/-- info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_countQueries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_countQueries

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_badWithin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_badWithin_le

/-- info: 'SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le

/-- info: 'SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le_sharper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le_sharper

/-- info: 'SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le_of_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.prob_coverage_within_le_of_family

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_terms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_terms

/-- info: 'SlhDsaSecurity.CollisionToDeviating.canonicalInput_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.canonicalInput_tree

/-- info: 'SlhDsaSecurity.CollisionToDeviating.exists_deviating_child' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.exists_deviating_child

/-- info: 'SlhDsaSecurity.DigestInputDistinct.messageInput_injective_of_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestInputDistinct.messageInput_injective_of_frame

/-- info: 'SlhDsaSecurity.DigestInputDistinct.separated_messageInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestInputDistinct.separated_messageInput

/-- info: 'SlhDsaSecurity.GrowthCharge.cache_value_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.cache_value_persists

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_cache_value_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_cache_value_le

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_cache_values_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_cache_values_le

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_cache_values_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_cache_values_mem_le

/-- info: 'SlhDsaSecurity.FreshDigest.fresh_messageDigest_instance_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.fresh_messageDigest_instance_uniform

/-- info: 'SlhDsaSecurity.FreshDigest.instanceAssignment_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.instanceAssignment_uniform

/-- info: 'SlhDsaSecurity.GrowthCharge.prob_cache_values_mem_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.prob_cache_values_mem_le'

/-- info: 'SlhDsaSecurity.FreshDigest.prob_instance_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.prob_instance_event_le

/-- info: 'SlhDsaSecurity.FreshDigest.prob_view_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.prob_view_event_le

/-- info: 'SlhDsaSecurity.FreshDigest.prob_tape_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.prob_tape_event_le

/-- info: 'SlhDsaSecurity.PerQueryBudget.union_exceeds_target' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.union_exceeds_target

/-- info: 'SlhDsaSecurity.PerQueryBudget.split_within_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.split_within_target

/-- info: 'SlhDsaSecurity.PerQueryBudget.union_exceeds_target_of_128' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.union_exceeds_target_of_128

/-- info: 'SlhDsaSecurity.PerQueryBudget.union_within_target_of_256' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.union_within_target_of_256

/-- info: 'SlhDsaSecurity.PerQueryBudget.classRate_le_target' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.classRate_le_target

/-- info: 'SlhDsaSecurity.PerQueryBudget.total_le_target' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.total_le_target

/-- info: 'SlhDsaSecurity.CombinedCharge.prob_combinedBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CombinedCharge.prob_combinedBad_le

/-- info: 'SlhDsaSecurity.CombinedCharge.prob_combinedBad_within_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CombinedCharge.prob_combinedBad_within_le

/-- info: 'SlhDsaSecurity.SecretGuessCharge.prob_secret_guessed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SecretGuessCharge.prob_secret_guessed_le

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_halves

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_classes

/-- info: 'SlhDsaSecurity.ClassCharge.prob_badWithinClasses_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.prob_badWithinClasses_le

/-- info: 'SlhDsaSecurity.SecretGuessCharge.prob_run_guesses_secret_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SecretGuessCharge.prob_run_guesses_secret_le

/-- info: 'SlhDsaSecurity.SeedDeferral.seed_query_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.seed_query_comm

/-- info: 'SlhDsaSecurity.SeedDeferral.transcript_indep_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.transcript_indep_of_seed

/-- info: 'SlhDsaSecurity.SeedDeferral.honest_result_indep_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.honest_result_indep_of_seed

/-- info: 'SlhDsaSecurity.SeedDeferral.honest_result_defer_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.honest_result_defer_seed

/-- info: 'SlhDsaSecurity.SeedDeferral.prob_honest_key_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.prob_honest_key_le

/-- info: 'SlhDsaSecurity.SeedDeferral.prob_any_honest_key_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.prob_any_honest_key_le

/-- info: 'SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_tree_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_tree_pair

/-- info: 'SlhDsaSecurity.QueryCached.cached_of_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.QueryCached.cached_of_hash

/-- info: 'SlhDsaSecurity.QueryCached.answer_cached_of_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.QueryCached.answer_cached_of_hash

/-- info: 'SlhDsaSecurity.CombinedCharge.separated_of_not_possible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CombinedCharge.separated_of_not_possible

/-- info: 'SlhDsaSecurity.ForsCoverageTerm.moment_le_of_few_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.moment_le_of_few_digests

/-- info: 'SlhDsaSecurity.Assembly.cap_defect_within_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.cap_defect_within_slack

/-- info: 'SlhDsaSecurity.ClassBudget.growthOn_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassBudget.growthOn_le_count

/-- info: 'SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_single_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_single_child

/-- info: 'SlhDsaSecurity.CacheReplay.run_eq_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.run_eq_replay

/--
info: 'SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.deviatingCollision_of_array

/-- info: 'SlhDsaSecurity.CacheReplay.tweakable_replayQuery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.tweakable_replayQuery

/--
info: 'SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathCollision

/--
info: 'SlhDsaSecurity.ForsCharge.deviatingCollision_of_compressionCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCharge.deviatingCollision_of_compressionCollision

/-- info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision

/-- info: 'SlhDsaSecurity.ForsLeafCharge.deviatingCollision_of_leafCollision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeafCharge.deviatingCollision_of_leafCollision

/-- info: 'SlhDsaSecurity.CanonicalCells.parentCell_eq_truncate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalCells.parentCell_eq_truncate

/-- info: 'SlhDsaSecurity.ForsLeafCharge.deviatingCollision_of_leafCollision_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeafCharge.deviatingCollision_of_leafCollision_canonical

/--
info: 'SlhDsaSecurity.ForsCharge.deviatingCollision_of_compressionCollision_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCharge.deviatingCollision_of_compressionCollision_canonical

/-- info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision_canonical

/-- info: 'SlhDsaSecurity.MerkleCharge.canonicalPair_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MerkleCharge.canonicalPair_fst

/-- info: 'SlhDsaSecurity.MerkleCharge.canonicalPair_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MerkleCharge.canonicalPair_snd

/--
info: 'SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathCollision_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathCollision_canonical

/--
info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_compressionCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_compressionCollision

/-- info: 'SlhDsaSecurity.CacheReplay.cached_of_queriesUnder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.cached_of_queriesUnder

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_bind

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_tweakable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_tweakable

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_head

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_tail

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_foldlM_get

/-- info: 'SlhDsaSecurity.CacheReplay.replayFold_eq_foldl' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.replayFold_eq_foldl

/-- info: 'SlhDsaSecurity.CacheReplay.replayFold_step_eq_tweakable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.replayFold_step_eq_tweakable

/-- info: 'SlhDsaSecurity.CacheReplay.foldl_finRange_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.foldl_finRange_take

/-- info: 'SlhDsaSecurity.PathEntry.pathInput_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PathEntry.pathInput_cached

/-- info: 'SlhDsaSecurity.WotsEntry.queriesUnder_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsEntry.queriesUnder_chain

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_bind_right' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_bind_right

/-- info: 'SlhDsaSecurity.CacheReplay.queriesUnder_compression' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_compression

/-- info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision_canonical_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainCollision_canonical_at

/-- info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_chainBranch

/--
info: 'SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathBranch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MerkleCharge.deviatingCollision_of_pathBranch

/--
info: 'SlhDsaSecurity.WotsCharge.deviatingCollision_of_compressionCollision_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsCharge.deviatingCollision_of_compressionCollision_canonical

/-- info: 'SlhDsaSecurity.HypertreeDispatch.cases_of_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HypertreeDispatch.cases_of_accepted

/--
info: 'SlhDsaSecurity.HypertreeDispatch.queriesUnder_rootFromSignature_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HypertreeDispatch.queriesUnder_rootFromSignature_tail

/-- info: 'SlhDsaSecurity.InputCoupling.probEvent_seedDerived_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.probEvent_seedDerived_le

/-- info: 'SlhDsaSecurity.InputCoupling.real_step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.real_step_eq

/-- info: 'SlhDsaSecurity.InputCoupling.evalDist_blind_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.evalDist_blind_step

/-- info: 'SlhDsaSecurity.InputCoupling.tvDist_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.tvDist_step_le

/-- info: 'SlhDsaSecurity.InputCoupling.step_eq_of_uncharged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.step_eq_of_uncharged

/-- info: 'SlhDsaSecurity.InputCoupling.real_bad_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.real_bad_monotone

/-- info: 'SlhDsaSecurity.InputCoupling.advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.advantage_le

/--
info: 'SlhDsaSecurity.InputCoupling.chargedStep_of_probEvent_bad_step_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.chargedStep_of_probEvent_bad_step_le

/-- info: 'SlhDsaSecurity.InputCoupling.probEvent_bad_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.probEvent_bad_step_le

/-- info: 'SlhDsaSecurity.InputCoupling.probEvent_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.probEvent_bad_le

/-- info: 'SlhDsaSecurity.InputCoupling.advantage_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.InputCoupling.advantage_le_two_mul

/-- info: 'SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pair

/--
info: 'SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathCollision

/-- info: 'SlhDsaSecurity.ForsDispatch.value_forsChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.value_forsChild

/--
info: 'SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathCollision_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathCollision_canonical

/--
info: 'SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathBranch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.deviatingCollision_of_pathBranch

/-- info: 'SlhDsaSecurity.ForsDispatch.ForsCollision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.ForsCollision

/--
info: 'SlhDsaSecurity.ForsDispatch.forsCollision_or_canonical_secrets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.forsCollision_or_canonical_secrets

/-- info: 'SlhDsaSecurity.ForsDispatch.leafIndex_div_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.leafIndex_div_lt

/--
info: 'SlhDsaSecurity.ForsDispatch.deviatingCollision_of_forsCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.deviatingCollision_of_forsCollision

/-- info: 'SlhDsaSecurity.BlindComparison.flag_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.flag_one

/-- info: 'SlhDsaSecurity.BlindComparison.prob_touched_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.prob_touched_eq

/-- info: 'SlhDsaSecurity.SeedDeferral.prob_run_meets_honest_key_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.prob_run_meets_honest_key_le

/-- info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_halves

/-- info: 'SlhDsaSecurity.GameBridge.verify_eq_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.verify_eq_replay

/-- info: 'SlhDsaSecurity.GameBridge.keygen_publicKey' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.keygen_publicKey

/-- info: 'SlhDsaSecurity.MainTheorem.probEvent_runAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.probEvent_runAll

/--
info: 'SlhDsaSecurity.WholeGameStructural.prob_combinedBad_whole_game_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.prob_combinedBad_whole_game_le

/-- info: 'SlhDsaSecurity.GameBridge.value_eq_cellsOfOutputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.value_eq_cellsOfOutputs

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_fresh

/-- info: 'SlhDsaSecurity.Presample.evalDist_prefill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prefill

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_evaluate

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_fresh_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_fresh_world

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_worldEvaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_worldEvaluate

/--
info: 'SlhDsaSecurity.WholeGameStructural.prob_badWithinClasses_whole_game_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.prob_badWithinClasses_whole_game_le

/-- info: 'SlhDsaSecurity.WeightedCharge.prob_badWeighted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.prob_badWeighted_le

/-- info: 'SlhDsaSecurity.WeightedCharge.weightedGrowth_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.weightedGrowth_le_count

/-- info: 'SlhDsaSecurity.Assembly.messageCount_le_slack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.messageCount_le_slack

/-- info: 'SlhDsaSecurity.Assembly.weighted_add_defect_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.weighted_add_defect_le

/-- info: 'SlhDsaSecurity.WeightedCharge.weightedGrowth_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.weightedGrowth_of_growth

/-- info: 'SlhDsaSecurity.WeightedCharge.jointGrowth_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.jointGrowth_le_count

/--
info: 'SlhDsaSecurity.WholeGameStructural.prob_badWeighted_whole_game_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.prob_badWeighted_whole_game_le

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_warmup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_warmup

/-- info: 'SlhDsaSecurity.Presample.run_liftM_probComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.run_liftM_probComp

/-- info: 'SlhDsaSecurity.Presample.evalDist_prepend_warmup_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_prepend_warmup_after

/-- info: 'SlhDsaSecurity.Presample.worldEvaluate_eq_liftM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.worldEvaluate_eq_liftM

/-- info: 'SlhDsaSecurity.Presample.run_worldWarmup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.run_worldWarmup

/-- info: 'SlhDsaSecurity.Presample.countAllHashes_liftM_probComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.countAllHashes_liftM_probComp

/-- info: 'SlhDsaSecurity.Presample.evalDist_counted_warmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.evalDist_counted_warmed

/-- info: 'SlhDsaSecurity.ForsLeaveOneOut.signingLimit_le_tapeBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.signingLimit_le_tapeBound

/-- info: 'SlhDsaSecurity.GameBridge.verifyInternal_of_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.verifyInternal_of_verify

/-- info: 'SlhDsaSecurity.GameBridge.hypertree_of_verifyInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.hypertree_of_verifyInternal

/-- info: 'SlhDsaSecurity.GameBridge.cases_of_replayed_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.cases_of_replayed_accept

/-- info: 'SlhDsaSecurity.BlindComparison.agreeOff_cacheFrom_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.agreeOff_cacheFrom_empty

/-- info: 'SlhDsaSecurity.BlindComparison.secretSeed_mem_children_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.secretSeed_mem_children_iff

/-- info: 'SlhDsaSecurity.BlindComparison.agreeOff_seedInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.agreeOff_seedInputs

/-- info: 'SlhDsaSecurity.TrackedQueries.card_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.card_le_count

/-- info: 'SlhDsaSecurity.TrackedQueries.meets_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.meets_one

/-- info: 'SlhDsaSecurity.TrackedQueries.prob_meets_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prob_meets_eq

/-- info: 'SlhDsaSecurity.TrackedQueries.prob_meets_real_eq_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prob_meets_real_eq_blind

/-- info: 'SlhDsaSecurity.TrackedQueries.prob_meets_blind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prob_meets_blind_le

/-- info: 'SlhDsaSecurity.TrackedQueries.prob_meets_real_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prob_meets_real_le

/-- info: 'SlhDsaSecurity.TrackedQueries.prfInput_node_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prfInput_node_eq

/-- info: 'SlhDsaSecurity.TrackedQueries.prfInput_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.prfInput_injective

/-- info: 'SlhDsaSecurity.TrackedQueries.locateNode_prfInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.locateNode_prfInput

/-- info: 'SlhDsaSecurity.TrackedQueries.children_of_prf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.children_of_prf

/-- info: 'SlhDsaSecurity.TrackedQueries.canonicalInput_eq_prfInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.canonicalInput_eq_prfInput

/-- info: 'SlhDsaSecurity.TrackedQueries.seedInputOf_of_isSeedInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.seedInputOf_of_isSeedInput

/-- info: 'SlhDsaSecurity.TrackedQueries.agreeOff_prfInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.agreeOff_prfInputs

/-- info: 'SlhDsaSecurity.WarmedGame.experiment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.experiment_eq

/-- info: 'SlhDsaSecurity.WarmedGame.map_warmedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.map_warmedRun

/-- info: 'SlhDsaSecurity.WarmedGame.evalDist_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.evalDist_outcome

/-- info: 'SlhDsaSecurity.WarmedGame.probEvent_warmed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.probEvent_warmed

/--
info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_warmed_halves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_warmed_halves

/-- info: 'SlhDsaSecurity.Averaging.probEvent_bind_pair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Averaging.probEvent_bind_pair_le

/-- info: 'SlhDsaSecurity.WarmedGame.warmedRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.warmedRun_eq

/-- info: 'SlhDsaSecurity.WarmedGame.probEvent_le_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.probEvent_le_of_tail

/-- info: 'SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_canonical

/-- info: 'SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_empty_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_empty_canonical

/-- info: 'SlhDsaSecurity.Averaging.support_eq_of_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Averaging.support_eq_of_evalDist_eq

/-- info: 'SlhDsaSecurity.WarmedGame.graphWalk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.graphWalk_eq

/-- info: 'SlhDsaSecurity.WarmedGame.mem_support_graphWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedGame.mem_support_graphWalk

/-- info: 'SlhDsaSecurity.WarmedCharges.mem_support_warmedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.mem_support_warmedRun

/-- info: 'SlhDsaSecurity.WarmedCharges.count_le_of_budget_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.count_le_of_budget_tail

/-- info: 'SlhDsaSecurity.WarmedCharges.walk_cache_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.walk_cache_canonical

/--
info: 'SlhDsaSecurity.WarmedCharges.prob_deviatingCollision_tail_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.prob_deviatingCollision_tail_le

/-- info: 'SlhDsaSecurity.CachedRun.run_eq_pure_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CachedRun.run_eq_pure_of_cached

/-- info: 'SlhDsaSecurity.CachedRun.eq_of_mem_support_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CachedRun.eq_of_mem_support_of_cached

/-- info: 'SlhDsaSecurity.WarmedCharges.not_messageInput_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.not_messageInput_canonical

/-- info: 'SlhDsaSecurity.WarmedCharges.cleanBad_walk_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.cleanBad_walk_cache

/-- info: 'SlhDsaSecurity.WarmedCharges.prob_combinedBad_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.prob_combinedBad_tail_le

/-- info: 'SlhDsaSecurity.WarmedSplit.run_rom_liftM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.run_rom_liftM

/-- info: 'SlhDsaSecurity.WarmedSplit.verify_liftM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.verify_liftM

/-- info: 'SlhDsaSecurity.WarmedSplit.keygenInternal_liftM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.keygenInternal_liftM

/-- info: 'SlhDsaSecurity.WarmedSplit.run_eq_replay_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.run_eq_replay_of_subset

/--
info: 'SlhDsaSecurity.WarmedSplit.keygenInternal_eq_replay_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.keygenInternal_eq_replay_of_subset

/-- info: 'SlhDsaSecurity.WarmedSplit.countQueries_query_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.countQueries_query_bind

/-- info: 'SlhDsaSecurity.WarmedSplit.mem_support_of_countAllHashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.mem_support_of_countAllHashes

/-- info: 'SlhDsaSecurity.WarmedSplit.mem_support_of_countQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.mem_support_of_countQueries

/-- info: 'SlhDsaSecurity.WarmedSplit.mem_support_counted_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.mem_support_counted_bind

/-- info: 'SlhDsaSecurity.WarmedSplit.split_afterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.split_afterSeeds

/-- info: 'SlhDsaSecurity.WarmedSplit.cases_of_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedSplit.cases_of_win

/-- info: 'SlhDsaSecurity.ForsBranch.deviatingCollision_or_secrets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsBranch.deviatingCollision_or_secrets

/-- info: 'SlhDsaSecurity.WarmedCharges.blindOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.blindOrder

/-- info: 'SlhDsaSecurity.WarmedCharges.mem_blindOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.mem_blindOrder

/-- info: 'SlhDsaSecurity.WarmedCharges.agreeOff_blindCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.agreeOff_blindCache

/-- info: 'SlhDsaSecurity.WarmedCharges.blindCache_seedInput_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.blindCache_seedInput_none

/-- info: 'SlhDsaSecurity.PathEntry.queriesUnder_pathInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PathEntry.queriesUnder_pathInput

/-- info: 'SlhDsaSecurity.FaultCharge.merkle_eq_wots_bind_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.merkle_eq_wots_bind_fold

/-- info: 'SlhDsaSecurity.FaultCharge.replay_agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.replay_agrees

/-- info: 'SlhDsaSecurity.FaultCharge.queriesUnder_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.queriesUnder_sequenceFin

/-- info: 'SlhDsaSecurity.FaultCharge.simulateQ_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.simulateQ_endpoints

/-- info: 'SlhDsaSecurity.FaultCharge.queriesUnder_wots_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.queriesUnder_wots_compression

/-- info: 'SlhDsaSecurity.FaultCharge.queriesUnder_wots_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.queriesUnder_wots_chain

/-- info: 'SlhDsaSecurity.FaultCharge.queriesUnder_merkle_wots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.queriesUnder_merkle_wots

/-- info: 'SlhDsaSecurity.FaultCharge.queriesUnder_merkle_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.queriesUnder_merkle_path

/-- info: 'SlhDsaSecurity.FaultCharge.endpoints_sign_eq_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.endpoints_sign_eq_cells

/--
info: 'SlhDsaSecurity.FaultCharge.deviatingCollision_of_layerCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.deviatingCollision_of_layerCollision

/--
info: 'SlhDsaSecurity.FaultCharge.deviatingCollision_or_residue_of_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.deviatingCollision_or_residue_of_fault

/--
info: 'SlhDsaSecurity.FaultCharge.deviatingCollision_or_residue_of_top_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FaultCharge.deviatingCollision_or_residue_of_top_fault

/-- info: 'SlhDsaSecurity.WarmedCharges.canonicalInput_of_not_prf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.canonicalInput_of_not_prf

/-- info: 'SlhDsaSecurity.WarmedCharges.blindCache_indep_of_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.blindCache_indep_of_secret

/-- info: 'SlhDsaSecurity.HonestProbes.queriesUnder_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.queriesUnder_shape

/-- info: 'SlhDsaSecurity.HonestProbes.query_bind_injective' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.query_bind_injective

/-- info: 'SlhDsaSecurity.HonestProbes.queriesUnder_query_bind_cases' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.queriesUnder_query_bind_cases

/-- info: 'SlhDsaSecurity.HonestProbes.probes_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_pure

/-- info: 'SlhDsaSecurity.HonestProbes.probes_query_bind' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_query_bind

/-- info: 'SlhDsaSecurity.HonestProbes.probes_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_bind

/-- info: 'SlhDsaSecurity.HonestProbes.probes_bind_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_bind_replay

/-- info: 'SlhDsaSecurity.HonestProbes.probes_hash' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_hash

/-- info: 'SlhDsaSecurity.HonestProbes.probes_shortHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_shortHash

/-- info: 'SlhDsaSecurity.HonestProbes.probes_shortHash_self' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_shortHash_self

/-- info: 'SlhDsaSecurity.HonestProbes.probes_tweakable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_tweakable

/-- info: 'SlhDsaSecurity.HonestProbes.probes_tweakable_self' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_tweakable_self

/-- info: 'SlhDsaSecurity.HonestProbes.probes_sequenceFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_sequenceFin

/-- info: 'SlhDsaSecurity.HonestProbes.probes_foldlM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_foldlM

/-- info: 'SlhDsaSecurity.HonestProbes.ordered_bytes_eq_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.ordered_bytes_eq_children

/-- info: 'SlhDsaSecurity.HonestProbes.replayFold_pathInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.replayFold_pathInput

/-- info: 'SlhDsaSecurity.HonestProbes.simulateQ_replay_foldlM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.simulateQ_replay_foldlM

/-- info: 'SlhDsaSecurity.HonestProbes.probes_pathFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_pathFold

/-- info: 'SlhDsaSecurity.HonestProbes.probes_pathFold_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_pathFold_of_eq

/-- info: 'SlhDsaSecurity.HonestProbes.replay_pathFold_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.replay_pathFold_of_eq

/-- info: 'SlhDsaSecurity.HonestProbes.childBytes_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.childBytes_singleton

/-- info: 'SlhDsaSecurity.HonestProbes.childBytes_pair' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.childBytes_pair

/-- info: 'SlhDsaSecurity.HonestProbes.derive_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.derive_replay

/-- info: 'SlhDsaSecurity.HonestProbes.tweakable_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.tweakable_replay

/-- info: 'SlhDsaSecurity.HonestProbes.chain_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.chain_replay

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_node_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_node_replay

/-- info: 'SlhDsaSecurity.HonestProbes.keygenInternal_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.keygenInternal_replay

/-- info: 'SlhDsaSecurity.HonestProbes.children_wotsHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.children_wotsHash

/-- info: 'SlhDsaSecurity.HonestProbes.replayCells_wotsPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.replayCells_wotsPosition

/-- info: 'SlhDsaSecurity.HonestProbes.canonicalInput_wotsPrf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonicalInput_wotsPrf

/-- info: 'SlhDsaSecurity.HonestProbes.canonicalInput_wotsHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonicalInput_wotsHash

/-- info: 'SlhDsaSecurity.HonestProbes.canonicalInput_wotsPk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonicalInput_wotsPk

/-- info: 'SlhDsaSecurity.HonestProbes.probes_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_chain

/-- info: 'SlhDsaSecurity.HonestProbes.probes_wots_publicKey' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_wots_publicKey

/-- info: 'SlhDsaSecurity.HonestProbes.canonicalInput_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonicalInput_tree

/-- info: 'SlhDsaSecurity.HonestProbes.probes_merkle_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_merkle_node

/-- info: 'SlhDsaSecurity.HonestProbes.probes_keygenInternal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_keygenInternal

/-- info: 'SlhDsaSecurity.HonestProbes.xor_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.xor_one_lt

/-- info: 'SlhDsaSecurity.HonestProbes.fors_secret_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_secret_replay

/-- info: 'SlhDsaSecurity.HonestProbes.fors_node_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_node_replay

/-- info: 'SlhDsaSecurity.HonestProbes.fors_sign_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_sign_replay

/-- info: 'SlhDsaSecurity.HonestProbes.canonical_forsSecret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonical_forsSecret

/-- info: 'SlhDsaSecurity.HonestProbes.canonical_forsLeaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonical_forsLeaf

/-- info: 'SlhDsaSecurity.HonestProbes.canonical_forsNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonical_forsNode

/-- info: 'SlhDsaSecurity.HonestProbes.probes_fors_node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_fors_node

/-- info: 'SlhDsaSecurity.HonestProbes.probes_fors_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_fors_sign

/-- info: 'SlhDsaSecurity.HonestProbes.fors_sign_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_sign_entry

/-- info: 'SlhDsaSecurity.HonestProbes.canonical_forsRoots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonical_forsRoots

/-- info: 'SlhDsaSecurity.HonestProbes.fors_combine_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_combine_eq

/-- info: 'SlhDsaSecurity.HonestProbes.fors_leaf_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_leaf_lt

/-- info: 'SlhDsaSecurity.HonestProbes.fors_leaf_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_leaf_div

/--
info: 'SlhDsaSecurity.HonestProbes.probes_fors_publicKeyFromSignature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_fors_publicKeyFromSignature

/--
info: 'SlhDsaSecurity.HonestProbes.wots_publicKeyFromSignature_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.wots_publicKeyFromSignature_replay

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_sign_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_sign_replay

/--
info: 'SlhDsaSecurity.HonestProbes.merkle_publicKeyFromSignature_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_publicKeyFromSignature_replay

/-- info: 'SlhDsaSecurity.HonestProbes.wots_sign_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.wots_sign_entry

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_sign_wots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_sign_wots

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_sign_authentication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_sign_authentication

/-- info: 'SlhDsaSecurity.HonestProbes.checksum_digit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.checksum_digit_le

/-- info: 'SlhDsaSecurity.HonestProbes.sibling_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.sibling_lt

/-- info: 'SlhDsaSecurity.HonestProbes.probes_wots_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_wots_sign

/--
info: 'SlhDsaSecurity.HonestProbes.probes_wots_publicKeyFromSignature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_wots_publicKeyFromSignature

/-- info: 'SlhDsaSecurity.HonestProbes.canonical_merkleNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.canonical_merkleNode

/-- info: 'SlhDsaSecurity.HonestProbes.probes_merkle_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_merkle_sign

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_combine_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_combine_eq

/--
info: 'SlhDsaSecurity.HonestProbes.probes_merkle_publicKeyFromSignature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_merkle_publicKeyFromSignature

/-- info: 'SlhDsaSecurity.HonestProbes.probes_hypertree_signLayers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_hypertree_signLayers

/-- info: 'SlhDsaSecurity.HonestProbes.Probes.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.Probes.mono

/-- info: 'SlhDsaSecurity.HonestProbes.forsAddress_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.forsAddress_eq

/-- info: 'SlhDsaSecurity.HonestProbes.probes_signInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_signInternal

/-- info: 'SlhDsaSecurity.HonestProbes.replayCells_warmCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.replayCells_warmCache

/-- info: 'SlhDsaSecurity.HonestProbes.warmCache_ne_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.warmCache_ne_none

/-- info: 'SlhDsaSecurity.HonestProbes.keygenInternal_probes_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.keygenInternal_probes_cached

/-- info: 'SlhDsaSecurity.HonestProbes.signInternal_probes_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signInternal_probes_cached

/-- info: 'SlhDsaSecurity.HonestProbes.run_keygenInternal_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.run_keygenInternal_eq_pure

/-- info: 'SlhDsaSecurity.HonestProbes.keygenInternal_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.keygenInternal_lift

/-- info: 'SlhDsaSecurity.HonestProbes.signInternal_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signInternal_lift

/--
info: 'SlhDsaSecurity.HonestProbes.run_keygenInternal_world_eq_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.run_keygenInternal_world_eq_pure

/-- info: 'SlhDsaSecurity.VerifierProbes.simulateQ_messageDigest' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.simulateQ_messageDigest

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_verify_fors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_verify_fors

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_verify_hypertree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_verify_hypertree

/-- info: 'SlhDsaSecurity.VerifierProbes.cached_hypertree_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.cached_hypertree_probe

/-- info: 'SlhDsaSecurity.VerifierProbes.fors_pathInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.fors_pathInput

/-- info: 'SlhDsaSecurity.VerifierProbes.fors_eq_trees_bind_compression' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.fors_eq_trees_bind_compression

/-- info: 'SlhDsaSecurity.VerifierProbes.simulateQ_forsTreeRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.simulateQ_forsTreeRoot

/-- info: 'SlhDsaSecurity.VerifierProbes.simulateQ_forsTrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.simulateQ_forsTrees

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_fors_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_fors_tree

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_fors_compression' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_fors_compression

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_fors_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_fors_leaf

/-- info: 'SlhDsaSecurity.VerifierProbes.queriesUnder_fors_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.queriesUnder_fors_path

/-- info: 'SlhDsaSecurity.VerifierProbes.cached_fors_compression_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.cached_fors_compression_probe

/-- info: 'SlhDsaSecurity.VerifierProbes.cached_fors_path_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.cached_fors_path_probe

/-- info: 'SlhDsaSecurity.VerifierProbes.cached_fors_leaf_probe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.cached_fors_leaf_probe

/--
info: 'SlhDsaSecurity.VerifierProbes.deviatingCollision_or_residue_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.deviatingCollision_or_residue_of_verified

/--
info: 'SlhDsaSecurity.VerifierProbes.deviatingCollision_or_secrets_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.deviatingCollision_or_secrets_of_verified

/-- info: 'SlhDsaSecurity.StripCached.run_simulateQ_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StripCached.run_simulateQ_strip

/-- info: 'SlhDsaSecurity.StripCached.queriesUnder_strip_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StripCached.queriesUnder_strip_none

/-- info: 'SlhDsaSecurity.SplitCharged.forsKeyOfDigest_address' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitCharged.forsKeyOfDigest_address

/-- info: 'SlhDsaSecurity.SplitCharged.cases_of_win_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitCharged.cases_of_win_charged

/-- info: 'SlhDsaSecurity.WarmedCharges.walk_cache_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.walk_cache_persists

/-- info: 'SlhDsaSecurity.WarmedCharges.value_replay_eq_walk_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmedCharges.value_replay_eq_walk_cells

/-- info: 'SlhDsaSecurity.DigestTape.recorder_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recorder_run_inl

/-- info: 'SlhDsaSecurity.DigestTape.recorder_run_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recorder_run_inr

/-- info: 'SlhDsaSecurity.DigestTape.rom_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.rom_run_inl

/-- info: 'SlhDsaSecurity.DigestTape.rom_run_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.rom_run_inr

/-- info: 'SlhDsaSecurity.DigestTape.paddedFrom_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.paddedFrom_bind

/-- info: 'SlhDsaSecurity.DigestTape.recorder_eq_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recorder_eq_rom

/-- info: 'SlhDsaSecurity.DigestTape.probEvent_recordedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.probEvent_recordedRun

/-- info: 'SlhDsaSecurity.DigestTape.record_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.record_prefix

/-- info: 'SlhDsaSecurity.DigestTape.record_prefix_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.record_prefix_padded

/-- info: 'SlhDsaSecurity.DigestTape.recorder_cache_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recorder_cache_mono

/-- info: 'SlhDsaSecurity.DigestTape.record_length_le_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.record_length_le_growth

/-- info: 'SlhDsaSecurity.DigestTape.prob_padding_prefix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_padding_prefix_le

/-- info: 'SlhDsaSecurity.DigestTape.prob_prefix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_prefix_le

/-- info: 'SlhDsaSecurity.DigestTape.padding_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.padding_length

/-- info: 'SlhDsaSecurity.DigestTape.padding_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.padding_neverFails

/-- info: 'SlhDsaSecurity.DigestTape.probEvent_paddedFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.probEvent_paddedFrom

/-- info: 'SlhDsaSecurity.DigestTape.viewTape_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.viewTape_uniform

/-- info: 'SlhDsaSecurity.DigestTape.prob_tape_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_tape_mem_le

/-- info: 'SlhDsaSecurity.DigestTape.prob_tape_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_tape_event_le

/-- info: 'SlhDsaSecurity.DigestTape.expectedUses_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.expectedUses_le

/-- info: 'SlhDsaSecurity.DigestTape.prob_tapeCovered_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_tapeCovered_le

/-- info: 'SlhDsaSecurity.DigestTape.tapeCovered_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.tapeCovered_of_prefix

/-- info: 'SlhDsaSecurity.DigestTape.padded_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.padded_length

/-- info: 'SlhDsaSecurity.DigestTape.prob_recordCovered_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_recordCovered_le

/-- info: 'SlhDsaSecurity.DigestTape.prob_recordCovered_within_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_recordCovered_within_le

/-- info: 'SlhDsaSecurity.DigestTape.prob_romEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.prob_romEvent_le

/--
info: 'SlhDsaSecurity.WotsResidueReduction.holds_early_chain_value_of_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsResidueReduction.holds_early_chain_value_of_residue

/-- info: 'SlhDsaSecurity.WotsResidueReduction.layerAt_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsResidueReduction.layerAt_eq

/-- info: 'SlhDsaSecurity.WotsResidueReduction.treeAt_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsResidueReduction.treeAt_le

/--
info: 'SlhDsaSecurity.WotsResidueReduction.exists_held_value_of_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsResidueReduction.exists_held_value_of_residue

/-- info: 'SlhDsaSecurity.WotsResidueReduction.heldValue_eq_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WotsResidueReduction.heldValue_eq_cell

/-- info: 'SlhDsaSecurity.CoverageTail.cacheCovered_of_forgeryCovered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.cacheCovered_of_forgeryCovered

/-- info: 'SlhDsaSecurity.CoverageTail.walk_cache_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.walk_cache_fresh

/-- info: 'SlhDsaSecurity.CoverageTail.recordCovered_of_cacheCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.recordCovered_of_cacheCovered

/-- info: 'SlhDsaSecurity.CoverageTail.prob_cacheCovered_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.prob_cacheCovered_tail_le

/-- info: 'SlhDsaSecurity.CoverageTail.prob_coverage_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.prob_coverage_tail_le

/-- info: 'SlhDsaSecurity.CoverageTail.prob_coverage_tail_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.prob_coverage_tail_le_of_budget

/-- info: 'SlhDsaSecurity.CoverageTail.parse_instance_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.parse_instance_eq_iff

/--
info: 'SlhDsaSecurity.CoverageTail.forsAddress_eq_of_parse_instance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.forsAddress_eq_of_parse_instance_eq

/-- info: 'SlhDsaSecurity.CoverageTail.parse_leaves_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageTail.parse_leaves_eq

/-- info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_allowances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_allowances

/--
info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_warmed_halves'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_warmed_halves'

/-- info: 'SlhDsaSecurity.StrippedGame.Extends.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.Extends.refl

/-- info: 'SlhDsaSecurity.StrippedGame.extends_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.extends_of_mem_support

/-- info: 'SlhDsaSecurity.StrippedGame.sign_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.sign_lift

/-- info: 'SlhDsaSecurity.StrippedGame.run_liftComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_liftComp

/-- info: 'SlhDsaSecurity.StrippedGame.run_strippedKeygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_strippedKeygen

/-- info: 'SlhDsaSecurity.StrippedGame.run_strippedSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_strippedSign

/-- info: 'SlhDsaSecurity.StrippedGame.run_liftM_counted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_liftM_counted

/-- info: 'SlhDsaSecurity.StrippedGame.run_liftM_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_liftM_state

/-- info: 'SlhDsaSecurity.StrippedGame.signingOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.signingOracle_eq

/-- info: 'SlhDsaSecurity.StrippedGame.run_signingOracleWith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_signingOracleWith

/-- info: 'SlhDsaSecurity.StrippedGame.run_signingOracleWith_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.run_signingOracleWith_congr

/-- info: 'SlhDsaSecurity.StrippedGame.countedRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.countedRun_bind

/-- info: 'SlhDsaSecurity.StrippedGame.evalDist_countedRun_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.evalDist_countedRun_congr

/--
info: 'SlhDsaSecurity.StrippedGame.evalDist_countedRun_signingOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.evalDist_countedRun_signingOracle

/-- info: 'SlhDsaSecurity.StrippedGame.evalDist_run_strippedAfterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.evalDist_run_strippedAfterSeeds

/-- info: 'SlhDsaSecurity.StrippedGame.strippedKeygen_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.strippedKeygen_eq

/-- info: 'SlhDsaSecurity.StrippedGame.strippedSign_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.strippedSign_eq

/-- info: 'SlhDsaSecurity.StrippedGame.honest_probes_not_in_warm_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.honest_probes_not_in_warm_cache

/-- info: 'SlhDsaSecurity.StrippedGame.honest_probes_not_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StrippedGame.honest_probes_not_canonical

/-- info: 'SlhDsaSecurity.CanonicalGraph.alwaysAvailable_merkleChild' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.alwaysAvailable_merkleChild

/-- info: 'SlhDsaSecurity.CanonicalGraph.children_alwaysAvailable_or_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.children_alwaysAvailable_or_singleton

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_zero

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_single_hash' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_single_hash

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_single_verification' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_single_verification

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_single_signing' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_single_signing

/-- info: 'SlhDsaSecurity.AdversaryQueries.countAllHashes_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.countAllHashes_map

/--
info: 'SlhDsaSecurity.AdversaryQueries.mem_support_counted_bind_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.mem_support_counted_bind_count

/-- info: 'SlhDsaSecurity.AdversaryQueries.run_counted_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.run_counted_bind

/-- info: 'SlhDsaSecurity.AdversaryQueries.run_adversaryImpl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.run_adversaryImpl

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_le_count_adversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_le_count_adversaryImpl

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_le_count_signingOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_le_count_signingOracle

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_le_count_adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_le_count_adversary

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_le_count_countQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_le_count_countQueries

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_le_total

/-- info: 'SlhDsaSecurity.CanonicalGraph.available_of_alwaysAvailable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.available_of_alwaysAvailable

/-- info: 'SlhDsaSecurity.CanonicalGraph.singleton_children_of_sensitive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.singleton_children_of_sensitive

/-- info: 'SlhDsaSecurity.CanonicalGraph.not_available_wotsPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.not_available_wotsPosition

/-- info: 'SlhDsaSecurity.CanonicalGraph.sensitive_of_child_wotsPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.sensitive_of_child_wotsPosition

/-- info: 'SlhDsaSecurity.CanonicalGraph.available_of_children_available' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.available_of_children_available

/-- info: 'SlhDsaSecurity.CanonicalGraph.sensitive_of_not_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.sensitive_of_not_available

/-- info: 'SlhDsaSecurity.SensitiveQuery.sensitive_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.sensitive_mono

/-- info: 'SlhDsaSecurity.SensitiveQuery.sensitive_initial' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.sensitive_initial

/-- info: 'SlhDsaSecurity.SensitiveQuery.coordinate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.coordinate_uniform

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_coordinate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_coordinate_eq

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_sensitive_le

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_record_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_record_sensitive_le

/-- info: 'SlhDsaSecurity.SensitiveQuery.probes_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.probes_run_inl

/-- info: 'SlhDsaSecurity.SensitiveQuery.probes_run_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.probes_run_inr

/-- info: 'SlhDsaSecurity.SensitiveQuery.length_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.length_le_count

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_probes_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_probes_sensitive_le

/-- info: 'SlhDsaSecurity.SensitiveQuery.not_unavailable_of_obtainable' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.not_unavailable_of_obtainable

/-- info: 'SlhDsaSecurity.RecordedQueries.run_simulateQ_map_writer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_simulateQ_map_writer

/-- info: 'SlhDsaSecurity.RecordedQueries.run_withAddCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_withAddCost

/-- info: 'SlhDsaSecurity.RecordedQueries.run_withAddCost_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_withAddCost_map

/-- info: 'SlhDsaSecurity.RecordedQueries.card_recordOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_recordOf

/-- info: 'SlhDsaSecurity.RecordedQueries.forget_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.forget_one

/-- info: 'SlhDsaSecurity.RecordedQueries.forget_mul' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.forget_mul

/-- info: 'SlhDsaSecurity.RecordedQueries.run_adversaryImpl_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_adversaryImpl_map

/-- info: 'SlhDsaSecurity.RecordedQueries.stateT_map_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.stateT_map_apply

/-- info: 'SlhDsaSecurity.RecordedQueries.run_liftM_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_liftM_base

/-- info: 'SlhDsaSecurity.RecordedQueries.run_liftM_inner' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_liftM_inner

/-- info: 'SlhDsaSecurity.RecordedQueries.run_recordedSigningOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_recordedSigningOracle

/-- info: 'SlhDsaSecurity.RecordedQueries.run_signingOracle_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_signingOracle_map

/--
info: 'SlhDsaSecurity.RecordedQueries.countQueries_eq_map_countRecorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.countQueries_eq_map_countRecorded

/-- info: 'SlhDsaSecurity.RecordedQueries.countQueries_verification_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.countQueries_verification_eq

/-- info: 'SlhDsaSecurity.RecordedQueries.map_recordedAfterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.map_recordedAfterSeeds

/-- info: 'SlhDsaSecurity.RecordedQueries.faithful_adversaryCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.faithful_adversaryCost

/-- info: 'SlhDsaSecurity.RecordedQueries.faithful_verifierCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.faithful_verifierCost

/-- info: 'SlhDsaSecurity.RecordedQueries.card_toAdd_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_toAdd_one

/-- info: 'SlhDsaSecurity.RecordedQueries.run_writer_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_writer_bind

/-- info: 'SlhDsaSecurity.RecordedQueries.run_recordedAdversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.run_recordedAdversaryImpl

/-- info: 'SlhDsaSecurity.RecordedQueries.card_eq_work_adversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_eq_work_adversaryImpl

/-- info: 'SlhDsaSecurity.RecordedQueries.card_eq_work_signingOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_eq_work_signingOracle

/-- info: 'SlhDsaSecurity.RecordedQueries.card_eq_work_adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_eq_work_adversary

/-- info: 'SlhDsaSecurity.RecordedQueries.countRecorded_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.countRecorded_pure

/-- info: 'SlhDsaSecurity.RecordedQueries.countRecorded_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.countRecorded_query_bind

/-- info: 'SlhDsaSecurity.RecordedQueries.card_eq_work_countRecorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_eq_work_countRecorded

/-- info: 'SlhDsaSecurity.RecordedQueries.card_eq_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_eq_work

/-- info: 'SlhDsaSecurity.RecordedQueries.card_toFinset_le_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_toFinset_le_work

/-- info: 'SlhDsaSecurity.RecordedQueries.card_toFinset_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedQueries.card_toFinset_le

/-- info: 'SlhDsaSecurity.LazyBridge.evalDist_bind_congr_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.evalDist_bind_congr_right

/-- info: 'SlhDsaSecurity.LazyBridge.flag_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.flag_one

/-- info: 'SlhDsaSecurity.LazyBridge.bad_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.bad_one

/-- info: 'SlhDsaSecurity.LazyBridge.probEvent_flag_refine_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.probEvent_flag_refine_eq

/--
info: 'SlhDsaSecurity.LazyBridge.probEvent_flag_refine_eq_of_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.probEvent_flag_refine_eq_of_commute

/-- info: 'SlhDsaSecurity.LazyBridge.probEvent_flag_refine_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.probEvent_flag_refine_le

/-- info: 'SlhDsaSecurity.RecordedBudget.map_countAllHashes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.map_countAllHashes

/-- info: 'SlhDsaSecurity.RecordedBudget.mem_support_countAllHashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.mem_support_countAllHashes

/-- info: 'SlhDsaSecurity.RecordedBudget.work_le_of_budget_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_le_of_budget_tail

/-- info: 'SlhDsaSecurity.RecordedBudget.work_le_of_budget_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_le_of_budget_recorded

/-- info: 'SlhDsaSecurity.RecordedBudget.card_toFinset_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.card_toFinset_le_of_budget

/-- info: 'SlhDsaSecurity.HonestGrowth.walk_cache_eq_warmCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.walk_cache_eq_warmCache

/-- info: 'SlhDsaSecurity.HonestGrowth.hash_eq_liftM' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.hash_eq_liftM

/-- info: 'SlhDsaSecurity.HonestGrowth.count_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.count_query

/-- info: 'SlhDsaSecurity.HonestGrowth.one_le_count_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.one_le_count_tweakable

/-- info: 'SlhDsaSecurity.HonestGrowth.growth_le_count_sub_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.growth_le_count_sub_keygen

/-- info: 'SlhDsaSecurity.HonestGrowth.growth_le_count_sub_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.growth_le_count_sub_four

/-- info: 'SlhDsaSecurity.GraphStakes.SensitiveNode.ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.SensitiveNode.ext

/-- info: 'SlhDsaSecurity.GraphStakes.inputOf_eq_canonicalInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.inputOf_eq_canonicalInput

/-- info: 'SlhDsaSecurity.GraphStakes.inputOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.inputOf_inj

/-- info: 'SlhDsaSecurity.GraphStakes.locate_inputOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.locate_inputOf

/-- info: 'SlhDsaSecurity.GraphStakes.closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.closed

/-- info: 'SlhDsaSecurity.GraphStakes.not_unavailable_of_obtainable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.not_unavailable_of_obtainable

/-- info: 'SlhDsaSecurity.GraphStakes.not_obtainable_wotsPosition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.not_obtainable_wotsPosition

/-- info: 'SlhDsaSecurity.GraphStakes.sensitiveNode_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.sensitiveNode_parent

/-- info: 'SlhDsaSecurity.GraphStakes.honestRevealed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.honestRevealed_le

/-- info: 'SlhDsaSecurity.GraphStakes.not_obtainable_forsPrf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.not_obtainable_forsPrf

/-- info: 'SlhDsaSecurity.GraphStakes.forsIndex_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.forsIndex_val

/--
info: 'SlhDsaSecurity.GraphStakes.forsSecret_signed_or_not_obtainable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.forsSecret_signed_or_not_obtainable

/-- info: 'SlhDsaSecurity.DrawnTable.prob_list_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DrawnTable.prob_list_sensitive_le

/-- info: 'SlhDsaSecurity.DrawnTable.missRun_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DrawnTable.missRun_length

/-- info: 'SlhDsaSecurity.DrawnTable.prob_missRun_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DrawnTable.prob_missRun_sensitive_le

/-- info: 'SlhDsaSecurity.DrawnTable.prob_mixture_missRun_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DrawnTable.prob_mixture_missRun_sensitive_le

/-- info: 'SlhDsaSecurity.DrawnTable.prob_table_first_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.DrawnTable.prob_table_first_sensitive_le

/-- info: 'SlhDsaSecurity.TableBlind.evalDist_bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableBlind.evalDist_bind_congr

/-- info: 'SlhDsaSecurity.TableBlind.evalDist_run_congr_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableBlind.evalDist_run_congr_of_step

/-- info: 'SlhDsaSecurity.TableBlind.probEvent_run_congr_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableBlind.probEvent_run_congr_of_step

/-- info: 'SlhDsaSecurity.TableBlind.prob_blind_run_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableBlind.prob_blind_run_sensitive_le

/-- info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_bound

/-- info: 'SlhDsaSecurity.HonestGrowth.pow_le_count_merkleNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.pow_le_count_merkleNode

/-- info: 'SlhDsaSecurity.HonestGrowth.pow_le_count_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.pow_le_count_keygen

/-- info: 'SlhDsaSecurity.HonestGrowth.growth_le_count_sub_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestGrowth.growth_le_count_sub_pow

/-- info: 'SlhDsaSecurity.GraphStakes.sensitive_inputOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.sensitive_inputOf

/-- info: 'SlhDsaSecurity.GraphStakes.sensitive_wotsClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.sensitive_wotsClaim

/-- info: 'SlhDsaSecurity.GraphStakes.sensitive_forsClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.sensitive_forsClaim

/-- info: 'SlhDsaSecurity.GraphStakes.claimedCount' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.claimedCount

/-- info: 'SlhDsaSecurity.GraphStakes.length_claimedCandidates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.length_claimedCandidates

/-- info: 'SlhDsaSecurity.HonestMessage.treeAt_succ_add_leafAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.treeAt_succ_add_leafAt

/-- info: 'SlhDsaSecurity.HonestMessage.revealedAt_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.revealedAt_succ

/-- info: 'SlhDsaSecurity.HonestMessage.honestMessage_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.honestMessage_succ

/-- info: 'SlhDsaSecurity.HonestMessage.honestMessage_eq_revealedAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.honestMessage_eq_revealedAt

/-- info: 'SlhDsaSecurity.HonestMessage.honestRevealed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.honestRevealed_eq

/-- info: 'SlhDsaSecurity.StalledRun.stalled_run_of_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.stalled_run_of_frozen

/-- info: 'SlhDsaSecurity.StalledRun.stalled_run_of_not_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.stalled_run_of_not_frozen

/-- info: 'SlhDsaSecurity.StalledRun.probEvent_flag_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.probEvent_flag_frozen

/-- info: 'SlhDsaSecurity.StalledRun.probEvent_flag_stalled_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.probEvent_flag_stalled_eq

/-- info: 'SlhDsaSecurity.StalledRun.evalDist_stalled_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.evalDist_stalled_congr

/-- info: 'SlhDsaSecurity.HonestMessage.signLayers_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.signLayers_get

/-- info: 'SlhDsaSecurity.HonestMessage.signLayers_wots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestMessage.signLayers_wots

/-- info: 'SlhDsaSecurity.OpenCache.cacheFrom_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.cacheFrom_congr

/-- info: 'SlhDsaSecurity.OpenCache.mem_openNodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.mem_openNodes

/-- info: 'SlhDsaSecurity.OpenCache.openCache_congr_of_agreeOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.openCache_congr_of_agreeOff

/-- info: 'SlhDsaSecurity.OpenCache.lazyProgram_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.lazyProgram_run_inl

/-- info: 'SlhDsaSecurity.OpenCache.lazyProgram_run_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.lazyProgram_run_inr

/-- info: 'SlhDsaSecurity.OpenCache.lazyProgram_step_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.lazyProgram_step_congr

/-- info: 'SlhDsaSecurity.OpenCache.lazyProgram_step_congr_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.lazyProgram_step_congr_graph

/-- info: 'SlhDsaSecurity.OpenCache.withFlag_run' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.withFlag_run

/-- info: 'SlhDsaSecurity.OpenCache.evalDist_stalled_lazyProgram_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.evalDist_stalled_lazyProgram_congr

/-- info: 'SlhDsaSecurity.withinBounds_structural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.withinBounds_structural

/-- info: 'SlhDsaSecurity.ChargedProbe.sensitive_iff_exists' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitive_iff_exists

/-- info: 'SlhDsaSecurity.ChargedProbe.sensitiveAt_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveAt_unique

/-- info: 'SlhDsaSecurity.ChargedProbe.flagged_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.flagged_run

/-- info: 'SlhDsaSecurity.ChargedProbe.lazyProgram_step_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.lazyProgram_step_inl

/-- info: 'SlhDsaSecurity.ChargedProbe.lazyProgram_step_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.lazyProgram_step_inr

/-- info: 'SlhDsaSecurity.ChargedProbe.lazyProgram_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.lazyProgram_neverFails

/-- info: 'SlhDsaSecurity.ChargedProbe.lazyProgram_cache_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.lazyProgram_cache_mono

/-- info: 'SlhDsaSecurity.ChargedProbe.flagged_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.flagged_neverFails

/-- info: 'SlhDsaSecurity.ChargedProbe.flagged_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.flagged_frozen

/-- info: 'SlhDsaSecurity.ChargedProbe.flagged_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.flagged_quiet

/-- info: 'SlhDsaSecurity.ChargedProbe.flag_iff_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.flag_iff_record

/-- info: 'SlhDsaSecurity.Assembly.defects_le_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.defects_le_five

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_counts

/-- info: 'SlhDsaSecurity.ClaimedProbes.clampStep_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClaimedProbes.clampStep_val

/-- info: 'SlhDsaSecurity.ClaimedProbes.forgedStep_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClaimedProbes.forgedStep_val

/-- info: 'SlhDsaSecurity.ClaimedProbes.sensitive_forgedClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClaimedProbes.sensitive_forgedClaim

/--
info: 'SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_tail

/--
info: 'SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_recorded

/--
info: 'SlhDsaSecurity.RecordedBudget.card_toFinset_append_le_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.card_toFinset_append_le_of_budget

/--
info: 'SlhDsaSecurity.RecordedBudget.card_toFinset_claimed_le_of_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.card_toFinset_claimed_le_of_budget

/-- info: 'SlhDsaSecurity.AdversaryQueries.work_add_keygen_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add_keygen_le_total

/-- info: 'SlhDsaSecurity.ChargedProbe.targets_of_sensitiveAt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.targets_of_sensitiveAt

/-- info: 'SlhDsaSecurity.ChargedProbe.targets_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.targets_unique

/-- info: 'SlhDsaSecurity.ChargedProbe.sum_targets_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sum_targets_length_le

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_list_sensitiveAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_list_sensitiveAt_le

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_list_sensitive_le_of_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_list_sensitive_le_of_sum

/-- info: 'SlhDsaSecurity.ChargedProbe.chargedBy_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.chargedBy_iff

/-- info: 'SlhDsaSecurity.ChargedProbe.targets_of_chargedBy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.targets_of_chargedBy

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_cell_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_cell_entry_le

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_cell_list_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_cell_list_le

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_run_cell_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_run_cell_le

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_run_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_run_sensitive_le

/-- info: 'SlhDsaSecurity.RedrawCell.evalDist_redraw_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.evalDist_redraw_coordinate

/-- info: 'SlhDsaSecurity.RedrawCell.prob_joint_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.prob_joint_sensitive_le

/-- info: 'SlhDsaSecurity.LazyBudget.mem_support_simulateQ_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.mem_support_simulateQ_of_step

/-- info: 'SlhDsaSecurity.LazyBudget.lazyAnswer_mem_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.lazyAnswer_mem_randomOracle

/-- info: 'SlhDsaSecurity.LazyBudget.mem_support_rom_of_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.mem_support_rom_of_lazy

/-- info: 'SlhDsaSecurity.LazyBudget.work_add_pow_le_of_budget_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.work_add_pow_le_of_budget_lazy

/--
info: 'SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_add_pow_le_of_budget_stripped

/-- info: 'SlhDsaSecurity.WarmProbes.warmCount_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_strip

/-- info: 'SlhDsaSecurity.WarmProbes.warmCount_adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_adversary

/-- info: 'SlhDsaSecurity.WarmProbes.warmCount_countQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_countQueries

/-- info: 'SlhDsaSecurity.WarmProbes.warmCount_strippedAfterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_strippedAfterSeeds

/-- info: 'SlhDsaSecurity.WarmProbes.exists_mem_warmProbes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.exists_mem_warmProbes

/-- info: 'SlhDsaSecurity.WarmProbes.warmCount_add_pow_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_add_pow_le_of_budget

/-- info: 'SlhDsaSecurity.WarmProbes.length_warmProbes_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.length_warmProbes_le_of_budget

/-- info: 'SlhDsaSecurity.ClaimedProbes.length_claimedCandidatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClaimedProbes.length_claimedCandidatesOf

/-- info: 'SlhDsaSecurity.WarmProbes.length_claimedEntries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.length_claimedEntries

/-- info: 'SlhDsaSecurity.WarmProbes.length_record_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.length_record_le_of_budget

/-- info: 'SlhDsaSecurity.SensitiveWarm.canonical_of_sensitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveWarm.canonical_of_sensitive

/-- info: 'SlhDsaSecurity.SensitiveWarm.warmCache_ne_none_of_sensitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveWarm.warmCache_ne_none_of_sensitive

/-- info: 'SlhDsaSecurity.StalledRun.expectation_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.expectation_frozen

/-- info: 'SlhDsaSecurity.StalledRun.expectation_stalled_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.StalledRun.expectation_stalled_eq

/-- info: 'SlhDsaSecurity.ChargedProbe.withFlag_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.withFlag_neverFails

/-- info: 'SlhDsaSecurity.ChargedProbe.withFlag_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.withFlag_frozen

/-- info: 'SlhDsaSecurity.ChargedProbe.withFlag_aiming_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.withFlag_aiming_quiet

/-- info: 'SlhDsaSecurity.ChargedProbe.expected_aiming_stalled_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.expected_aiming_stalled_eq

/-- info: 'SlhDsaSecurity.ChargedProbe.withFlag_charged_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.withFlag_charged_quiet

/-- info: 'SlhDsaSecurity.ChargedProbe.prob_charged_stalled_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.prob_charged_stalled_eq

/-- info: 'SlhDsaSecurity.ChargedProbe.sum_tsum_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sum_tsum_comm

/-- info: 'SlhDsaSecurity.RedrawCell.prob_charged_index_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.prob_charged_index_le

/-- info: 'SlhDsaSecurity.ChargedProbe.sum_weighted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sum_weighted_le

/-- info: 'SlhDsaSecurity.RedrawCell.prob_sensitive_run_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.prob_sensitive_run_le

/-- info: 'SlhDsaSecurity.CacheAvailability.mem_signedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.mem_signedAt

/-- info: 'SlhDsaSecurity.CacheAvailability.signedAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.signedAt_mono

/-- info: 'SlhDsaSecurity.CacheAvailability.availableAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.availableAt_mono

/-- info: 'SlhDsaSecurity.CacheAvailability.availableAt_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.availableAt_closed

/-- info: 'SlhDsaSecurity.CacheAvailability.lazyProgram_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.lazyProgram_persists

/-- info: 'SlhDsaSecurity.CacheAvailability.lazyProgram_run_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.lazyProgram_run_persists

/-- info: 'SlhDsaSecurity.SplitRouted.deviatingCollision_at_walk_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.deviatingCollision_at_walk_cells

/-- info: 'SlhDsaSecurity.SplitRouted.honestForsKey_eq_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.honestForsKey_eq_value

/-- info: 'SlhDsaSecurity.SplitRouted.honestMessage_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.honestMessage_zero

/-- info: 'SlhDsaSecurity.SplitRouted.honestRevealed_eq_revealedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.honestRevealed_eq_revealedAt

/-- info: 'SlhDsaSecurity.SplitRouted.sensitive_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.sensitive_of_residue

/-- info: 'SlhDsaSecurity.SplitRouted.signed_or_sensitive_of_secrets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.signed_or_sensitive_of_secrets

/-- info: 'SlhDsaSecurity.LazyBridge.probEvent_flag_two_handlers_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBridge.probEvent_flag_two_handlers_eq

/-- info: 'SlhDsaSecurity.OpenCache.openCache_congr_of_not_sensitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.openCache_congr_of_not_sensitive

/-- info: 'SlhDsaSecurity.OpenCache.lazyProgram_step_congr_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.lazyProgram_step_congr_available

/-- info: 'SlhDsaSecurity.CoverageRouted.forsIndex_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.forsIndex_inj

/-- info: 'SlhDsaSecurity.CoverageRouted.messageInput_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.messageInput_ne

/-- info: 'SlhDsaSecurity.CoverageRouted.forgeryCovered_of_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.forgeryCovered_of_witnesses

/--
info: 'SlhDsaSecurity.CoverageRouted.parse_instance_eq_of_forsKeyOfDigest_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.parse_instance_eq_of_forsKeyOfDigest_eq

/-- info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_agree

/-- info: 'SlhDsaSecurity.ChargedProbe.probEvent_sensitiveFlagged_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.probEvent_sensitiveFlagged_eq

/-- info: 'SlhDsaSecurity.Extraction.HypertreeChain.signLayers_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.signLayers_succ

/-- info: 'SlhDsaSecurity.Extraction.HypertreeChain.xmss_eq_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.xmss_eq_sign

/--
info: 'SlhDsaSecurity.Extraction.HypertreeChain.rootFromSignature_fault_or_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.rootFromSignature_fault_or_signed

/--
info: 'SlhDsaSecurity.Extraction.HypertreeChain.verify_fault_or_fors_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.verify_fault_or_fors_signed

/-- info: 'SlhDsaSecurity.ForsDispatch.fors_auth_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.fors_auth_index

/-- info: 'SlhDsaSecurity.ForsDispatch.sign_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.sign_apply

/--
info: 'SlhDsaSecurity.ForsDispatch.forsCollision_or_canonical_signature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDispatch.forsCollision_or_canonical_signature

/-- info: 'SlhDsaSecurity.CanonicalSignature.eq_signInternal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalSignature.eq_signInternal

/-- info: 'SlhDsaSecurity.CanonicalSignature.signature_eq_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalSignature.signature_eq_toBytes

/-- info: 'SlhDsaSecurity.CanonicalSignature.not_fresh_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalSignature.not_fresh_of_canonical

/--
info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_flag_iff_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_flag_iff_record

/-- info: 'SlhDsaSecurity.ChargedProbe.sensitive_of_sensitiveEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitive_of_sensitiveEntry

/--
info: 'SlhDsaSecurity.ChargedProbe.probEvent_sensitiveFlagged_eq_withFlag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.probEvent_sensitiveFlagged_eq_withFlag

/-- info: 'SlhDsaSecurity.RedrawCell.rom_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.rom_persists

/-- info: 'SlhDsaSecurity.RedrawCell.lazyProgram_total_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.lazyProgram_total_run

/-- info: 'SlhDsaSecurity.RedrawCell.probEvent_rom_eq_lazyProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.probEvent_rom_eq_lazyProgram

/-- info: 'SlhDsaSecurity.RedrawCell.unionCache_cacheQuery_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_cacheQuery_open

/-- info: 'SlhDsaSecurity.RedrawCell.unionCache_cacheQuery_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_cacheQuery_fresh

/-- info: 'SlhDsaSecurity.RedrawCell.compatible_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.compatible_empty

/-- info: 'SlhDsaSecurity.RedrawCell.rom_union_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.rom_union_step

/-- info: 'SlhDsaSecurity.RedrawCell.compatible_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.compatible_step

/-- info: 'SlhDsaSecurity.RedrawCell.probEvent_rom_eq_lazy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.probEvent_rom_eq_lazy

/-- info: 'SlhDsaSecurity.RedrawCell.probEvent_table_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.probEvent_table_congr

/-- info: 'SlhDsaSecurity.RedrawCell.probEvent_flag_eq_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.probEvent_flag_eq_record

/-- info: 'SlhDsaSecurity.RedrawCell.prob_game_sensitive_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.prob_game_sensitive_le

/-- info: 'SlhDsaSecurity.RedrawCell.openNodes_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.openNodes_total

/-- info: 'SlhDsaSecurity.RedrawCell.openCache_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.openCache_total

/-- info: 'SlhDsaSecurity.RedrawCell.unionCache_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_empty

/-- info: 'SlhDsaSecurity.CacheAvailability.isMessageInput_of_signerRandomised' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.isMessageInput_of_signerRandomised

/-- info: 'SlhDsaSecurity.CacheAvailability.signerRandomised_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.signerRandomised_mono

/-- info: 'SlhDsaSecurity.CacheAvailability.randomizer_eq_of_signerRandomised' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.randomizer_eq_of_signerRandomised

/-- info: 'SlhDsaSecurity.RandomizerGate.randomizerInput_prf_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.randomizerInput_prf_inj

/-- info: 'SlhDsaSecurity.RandomizerGate.prfGuess_randomizerInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prfGuess_randomizerInput

/-- info: 'SlhDsaSecurity.RandomizerGate.prob_run_randomizerInput_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prob_run_randomizerInput_le

/-- info: 'SlhDsaSecurity.RandomizerGate.canonicalInput_ne_randomizerInput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.canonicalInput_ne_randomizerInput

/-- info: 'SlhDsaSecurity.RandomizerGate.card_add_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.card_add_card_le

/-- info: 'SlhDsaSecurity.RandomizerGate.prob_prf_eq_publicSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prob_prf_eq_publicSeed

/-- info: 'SlhDsaSecurity.Assembly.defects_le_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.defects_le_six

/-- info: 'SlhDsaSecurity.RedrawCell.splitTable_fst_secretSeed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.splitTable_fst_secretSeed

/-- info: 'SlhDsaSecurity.RedrawCell.splitTable_fullOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.splitTable_fullOutput

/-- info: 'SlhDsaSecurity.RedrawCell.openCache_total_eq_warmCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.openCache_total_eq_warmCache

/-- info: 'SlhDsaSecurity.RedrawCell.prob_game_sensitive_honest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.prob_game_sensitive_honest_le

/-- info: 'SlhDsaSecurity.RandomizerGate.messageInput_eq_randomizerInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.messageInput_eq_randomizerInput

/-- info: 'SlhDsaSecurity.RandomizerGate.messageInput_eq_randomizerInput_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.messageInput_eq_randomizerInput_iff

/-- info: 'SlhDsaSecurity.HonestProbes.probes_sign_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_sign_none

/-- info: 'SlhDsaSecurity.HonestProbes.probes_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.probes_sign

/-- info: 'SlhDsaSecurity.RedrawCell.sensitive_iff_off_or_at_seed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.sensitive_iff_off_or_at_seed

/-- info: 'SlhDsaSecurity.RedrawCell.sensitiveOffSeed_iff_exists' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.sensitiveOffSeed_iff_exists

/-- info: 'SlhDsaSecurity.AdversaryQueries.servedCount_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.servedCount_append

/--
info: 'SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_adversary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_adversary

/--
info: 'SlhDsaSecurity.AdversaryQueries.work_add_keygen_add_served_le_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add_keygen_add_served_le_total

/--
info: 'SlhDsaSecurity.RecordedBudget.work_add_pow_add_served_le_of_budget_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_add_pow_add_served_le_of_budget_tail

/--
info: 'SlhDsaSecurity.RecordedBudget.card_toFinset_append_le_of_budget_served' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.card_toFinset_append_le_of_budget_served

/-- info: 'SlhDsaSecurity.Assembly.defects_add_served_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.defects_add_served_le

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_two_slacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_two_slacks

/-- info: 'SlhDsaSecurity.Assembly.le_target_of_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_served

/-- info: 'SlhDsaSecurity.RedrawCell.open_seedAndRoot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.open_seedAndRoot

/-- info: 'SlhDsaSecurity.AdversaryQueries.two_le_count_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.two_le_count_sign

/-- info: 'SlhDsaSecurity.RandomizerGate.prob_truncate_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prob_truncate_eq

/-- info: 'SlhDsaSecurity.RandomizerGate.prob_randomizerHitsSeed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prob_randomizerHitsSeed_le

/-- info: 'SlhDsaSecurity.RandomizerGate.cleanBad_of_canonical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.cleanBad_of_canonical

/--
info: 'SlhDsaSecurity.RandomizerGate.prob_randomizerHitsSeed_run_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomizerGate.prob_randomizerHitsSeed_run_le

/-- info: 'SlhDsaSecurity.AdversaryQueries.le_count_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.le_count_query_bind

/-- info: 'SlhDsaSecurity.ClassGrowth.classCost_inr_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.classCost_inr_hash

/-- info: 'SlhDsaSecurity.ClassGrowth.growthOn_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_step

/-- info: 'SlhDsaSecurity.ClassGrowth.growthOn_le_classCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_le_classCount

/--
info: 'SlhDsaSecurity.SensitiveExpectation.prob_run_sensitive_expected_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveExpectation.prob_run_sensitive_expected_le

/-- info: 'SlhDsaSecurity.SensitiveExpectation.expected_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveExpectation.expected_length_le

/-- info: 'SlhDsaSecurity.SensitiveExpectation.prob_run_sensitive_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveExpectation.prob_run_sensitive_le'

/-- info: 'SlhDsaSecurity.OpenCache.reading_step_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.reading_step_congr

/-- info: 'SlhDsaSecurity.HonestProbes.fors_sign_secret_cell' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_sign_secret_cell

/-- info: 'SlhDsaSecurity.HonestProbes.fors_sign_authentication_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.fors_sign_authentication_cell

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_sign_authentication_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_sign_authentication_cell

/-- info: 'SlhDsaSecurity.HonestProbes.merkle_sign_wots_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.merkle_sign_wots_cell

/-- info: 'SlhDsaSecurity.ClassExpectation.expected_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_bind

/-- info: 'SlhDsaSecurity.ClassExpectation.expected_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_map

/-- info: 'SlhDsaSecurity.ClassExpectation.expected_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_const_add

/-- info: 'SlhDsaSecurity.ClassExpectation.run_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.run_neverFails

/-- info: 'SlhDsaSecurity.ClassExpectation.prob_bad_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.prob_bad_le_expected

/-- info: 'SlhDsaSecurity.RecordedBudget.card_add_served_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.card_add_served_le_of_budget

/-- info: 'SlhDsaSecurity.WriterState.run_toStateful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.run_toStateful

/-- info: 'SlhDsaSecurity.WriterState.run_statefulSigningOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.run_statefulSigningOracle

/-- info: 'SlhDsaSecurity.ClassExpectation.expected_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_add

/-- info: 'SlhDsaSecurity.ClassExpectation.expected_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_le_of_le

/-- info: 'SlhDsaSecurity.ClassExpectation.add_le_of_shared_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.add_le_of_shared_budget

/-- info: 'SlhDsaSecurity.HonestProbes.subtree_root_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.subtree_root_cell

/-- info: 'SlhDsaSecurity.HonestProbes.signLayers_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signLayers_succ_eq

/-- info: 'SlhDsaSecurity.HonestProbes.signLayers_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signLayers_head

/-- info: 'SlhDsaSecurity.HonestProbes.signLayers_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signLayers_tail

/-- info: 'SlhDsaSecurity.HonestProbes.signLayers_head_wots_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signLayers_head_wots_cell

/--
info: 'SlhDsaSecurity.HonestProbes.signLayers_head_authentication_cell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HonestProbes.signLayers_head_authentication_cell

/-- info: 'SlhDsaSecurity.HypertreeDispatch.cases_of_accepted_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HypertreeDispatch.cases_of_accepted_signed

/-- info: 'SlhDsaSecurity.ForsBranch.deviatingCollision_or_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsBranch.deviatingCollision_or_canonical

/-- info: 'SlhDsaSecurity.CanonicalSplit.cases_of_win_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalSplit.cases_of_win_canonical

/--
info: 'SlhDsaSecurity.VerifierProbes.deviatingCollision_or_canonical_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierProbes.deviatingCollision_or_canonical_of_verified

/-- info: 'SlhDsaSecurity.WriterState.run_withAddCost_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.run_withAddCost_apply

/-- info: 'SlhDsaSecurity.WriterState.run_simulateQ_withAddCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.run_simulateQ_withAddCost

/-- info: 'SlhDsaSecurity.WriterState.simulateQ_run_addCostOracle_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.simulateQ_run_addCostOracle_map

/-- info: 'SlhDsaSecurity.WalkDefects.probEvent_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.probEvent_bind_le

/-- info: 'SlhDsaSecurity.WalkDefects.probEvent_bind_le_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.probEvent_bind_le_of_prefix

/-- info: 'SlhDsaSecurity.WalkDefects.probEvent_bind_pair_split_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.probEvent_bind_pair_split_le

/-- info: 'SlhDsaSecurity.WalkDefects.prob_prf_eq_publicSeed_seeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.prob_prf_eq_publicSeed_seeds

/-- info: 'SlhDsaSecurity.WalkDefects.prob_prf_eq_publicSeed_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.prob_prf_eq_publicSeed_walk

/-- info: 'SlhDsaSecurity.WalkDefects.probEvent_le_of_tail_of_seeds_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.probEvent_le_of_tail_of_seeds_ne

/-- info: 'SlhDsaSecurity.WalkDefects.value_topNode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.value_topNode

/-- info: 'SlhDsaSecurity.WalkDefects.outputs_coordinate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.outputs_coordinate_uniform

/-- info: 'SlhDsaSecurity.WalkDefects.prob_possible_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.prob_possible_walk

/--
info: 'SlhDsaSecurity.WalkDefects.probEvent_le_of_tail_of_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkDefects.probEvent_le_of_tail_of_separated

/-- info: 'SlhDsaSecurity.Target.prob_bad_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Target.prob_bad_walk

/-- info: 'SlhDsaSecurity.Target.probEvent_le_of_good_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Target.probEvent_le_of_good_walk

/-- info: 'SlhDsaSecurity.Target.allowance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Target.allowance

/-- info: 'SlhDsaSecurity.Target.target_of_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.Target.target_of_obligations

/-- info: 'SlhDsaSecurity.KeygenValue.run_recordedAfterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenValue.run_recordedAfterSeeds

/-- info: 'SlhDsaSecurity.RecordedPhase.run_tell_liftM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedPhase.run_tell_liftM

/-- info: 'SlhDsaSecurity.RecordedPhase.run_unchargedPhase_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedPhase.run_unchargedPhase_inr

/-- info: 'SlhDsaSecurity.RecordedPhase.phase_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedPhase.phase_eq

/-- info: 'SlhDsaSecurity.RecordedPhase.run_phase_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedPhase.run_phase_counted

/-- info: 'SlhDsaSecurity.KeygenBudget.pow_le_count_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenBudget.pow_le_count_tail

/-- info: 'SlhDsaSecurity.KeygenBudget.pow_le_count_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenBudget.pow_le_count_of_mem_support

/-- info: 'SlhDsaSecurity.KeygenBudget.pow_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenBudget.pow_le_of_budget

/-- info: 'SlhDsaSecurity.RoutedSplit.mem_claimedCandidates_wots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.mem_claimedCandidates_wots

/-- info: 'SlhDsaSecurity.RoutedSplit.mem_claimedCandidates_fors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.mem_claimedCandidates_fors

/-- info: 'SlhDsaSecurity.RoutedSplit.cases_of_win_routed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.cases_of_win_routed

/-- info: 'SlhDsaSecurity.RoutedSplit.queriesUnder_verify_message' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.queriesUnder_verify_message

/-- info: 'SlhDsaSecurity.RoutedSplit.cached_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.cached_digest

/-- info: 'SlhDsaSecurity.RoutedSplit.cases_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.cases_of_canonical

/-- info: 'SlhDsaSecurity.RoutedSplit.cases_of_win_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.cases_of_win_three

/-- info: 'SlhDsaSecurity.RecordedPhase.faithful_phaseCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedPhase.faithful_phaseCost

/-- info: 'SlhDsaSecurity.LinkedGame.simulateQ_liftWorld' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LinkedGame.simulateQ_liftWorld

/-- info: 'SlhDsaSecurity.LinkedGame.run_simulateQ_ofLift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LinkedGame.run_simulateQ_ofLift

/-- info: 'SlhDsaSecurity.LinkedGame.run_unchargedPhase_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LinkedGame.run_unchargedPhase_lift

/-- info: 'SlhDsaSecurity.LinkedGame.recordedAfterSeedsAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LinkedGame.recordedAfterSeedsAt_eq

/--
info: 'SlhDsaSecurity.Address.setTypeAndClear_fields' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Address.setTypeAndClear_fields

/--
info: 'SlhDsaSecurity.Address.toBytes_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Address.toBytes_length

/--
info: 'SlhDsaSecurity.AddressType.code_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AddressType.code_injective

/--
info: 'SlhDsaSecurity.AdversaryQueries.hash_eq_query' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.hash_eq_query

/--
info: 'SlhDsaSecurity.AdversaryQueries.one_le_count_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.one_le_count_query_bind

/--
info: 'SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_adversaryImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_adversaryImpl

/--
info: 'SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_signingOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AdversaryQueries.work_add_served_le_count_signingOracle

/--
info: 'SlhDsaSecurity.Assembly.capFail_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.capFail_eq

/--
info: 'SlhDsaSecurity.Assembly.defect_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.defect_eq

/--
info: 'SlhDsaSecurity.Assembly.half_add_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.half_add_half

/--
info: 'SlhDsaSecurity.Assembly.slack_or_few' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.slack_or_few

/--
info: 'SlhDsaSecurity.Assembly.structural_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.structural_eq

/--
info: 'SlhDsaSecurity.Assembly.target_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.target_eq

/--
info: 'SlhDsaSecurity.Assembly.target_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.target_eq_half

/--
info: 'SlhDsaSecurity.BlindComparison.AgreeOff.cacheQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.AgreeOff.cacheQuery

/--
info: 'SlhDsaSecurity.BlindComparison.agreeOff_cacheFrom' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.agreeOff_cacheFrom

/--
info: 'SlhDsaSecurity.BlindComparison.flag_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.flag_persists

/--
info: 'SlhDsaSecurity.BlindComparison.tagged_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.tagged_neverFails

/--
info: 'SlhDsaSecurity.BlindKey.coordinate_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindKey.coordinate_probability

/--
info: 'SlhDsaSecurity.BlindKey.expectedGuesses_add_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindKey.expectedGuesses_add_cost_le

/--
info: 'SlhDsaSecurity.BlindKey.expectedGuesses_le_of_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindKey.expectedGuesses_le_of_cap

/--
info: 'SlhDsaSecurity.BlindKey.hit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindKey.hit_probability_le

/--
info: 'SlhDsaSecurity.CacheAvailability.Persists.refl' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.Persists.refl

/--
info: 'SlhDsaSecurity.CacheAvailability.Persists.trans' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.Persists.trans

/--
info: 'SlhDsaSecurity.CacheAvailability.availableAt_revealed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.availableAt_revealed_le

/--
info: 'SlhDsaSecurity.CacheAvailability.lazyProgram_hash_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.lazyProgram_hash_persists

/--
info: 'SlhDsaSecurity.CacheAvailability.persists_cacheQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.persists_cacheQuery

/--
info: 'SlhDsaSecurity.CacheAvailability.unavailableAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheAvailability.unavailableAt_eq

/--
info: 'SlhDsaSecurity.CacheReplay.cache_value_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.cache_value_persists

/--
info: 'SlhDsaSecurity.CacheReplay.hash_replayQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.hash_replayQuery

/--
info: 'SlhDsaSecurity.CacheReplay.queriesUnder_hash' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_hash

/--
info: 'SlhDsaSecurity.CacheReplay.queriesUnder_shortHash' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_shortHash

/--
info: 'SlhDsaSecurity.CacheReplay.queriesUnder_tweakable_self' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.queriesUnder_tweakable_self

/--
info: 'SlhDsaSecurity.CacheReplay.shortHash_replayQuery' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.shortHash_replayQuery

/--
info: 'SlhDsaSecurity.CacheReplay.step_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.step_cached

/--
info: 'SlhDsaSecurity.CacheReplay.step_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheReplay.step_shape

/--
info: 'SlhDsaSecurity.CanonicalCells.parentCell_tweakable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalCells.parentCell_tweakable

/--
info: 'SlhDsaSecurity.CanonicalGraph.Node.child_rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Node.child_rank_lt

/--
info: 'SlhDsaSecurity.CanonicalGraph.Node.rank_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Node.rank_le

/--
info: 'SlhDsaSecurity.CanonicalGraph.ParsedInput.firstHiddenChild_none_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.ParsedInput.firstHiddenChild_none_iff

/--
info: 'SlhDsaSecurity.CanonicalGraph.ParsedInput.firstHiddenChild_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.ParsedInput.firstHiddenChild_some

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.AgreesOutside.assign' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.AgreesOutside.assign

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.cacheFrom_lookup

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.full_cache_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.full_cache_lookup

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.input_eq_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.input_eq_target

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.input_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.input_separated

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.mem_order' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.mem_order

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.order_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.order_nodup

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.order_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.order_pairwise

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.program_eq_cacheFrom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.program_eq_cacheFrom

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.splitTable_bijective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.splitTable_bijective

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.splitTable_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.splitTable_uniform

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.value_eq_of_cache_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.value_eq_of_cache_agreement

/--
info: 'SlhDsaSecurity.CanonicalGraph.Programming.warmup_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.Programming.warmup_uniform

/--
info: 'SlhDsaSecurity.CanonicalGraph.StructuralNode.address_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.StructuralNode.address_injective

/--
info: 'SlhDsaSecurity.CanonicalGraph.StructuralNode.child_rank_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.StructuralNode.child_rank_lt

/--
info: 'SlhDsaSecurity.CanonicalGraph.StructuralNode.rank_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.StructuralNode.rank_pos

/--
info: 'SlhDsaSecurity.CanonicalGraph.blindProbe_of_parse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.blindProbe_of_parse

/--
info: 'SlhDsaSecurity.CanonicalGraph.canonicalInput_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.canonicalInput_congr

/--
info: 'SlhDsaSecurity.CanonicalGraph.canonicalInput_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.canonicalInput_eq_iff

/--
info: 'SlhDsaSecurity.CanonicalGraph.canonicalInput_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.canonicalInput_parent

/--
info: 'SlhDsaSecurity.CanonicalGraph.childBytes_eq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.childBytes_eq_iff

/--
info: 'SlhDsaSecurity.CanonicalGraph.childBytes_ofFn' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.childBytes_ofFn

/--
info: 'SlhDsaSecurity.CanonicalGraph.child_index_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.child_index_lt

/--
info: 'SlhDsaSecurity.CanonicalGraph.fors_secret_cell' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.fors_secret_cell

/--
info: 'SlhDsaSecurity.CanonicalGraph.hypertree_root_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.hypertree_root_cell

/--
info: 'SlhDsaSecurity.CanonicalGraph.keygen_root_cell' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.keygen_root_cell

/--
info: 'SlhDsaSecurity.CanonicalGraph.merkleChild_rank' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.merkleChild_rank

/--
info: 'SlhDsaSecurity.CanonicalGraph.merkleNode_rank' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.merkleNode_rank

/--
info: 'SlhDsaSecurity.CanonicalGraph.message_canonical_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.message_canonical_ne

/--
info: 'SlhDsaSecurity.CanonicalGraph.parseInput_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.parseInput_canonical

/--
info: 'SlhDsaSecurity.CanonicalGraph.parseInput_canonical_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.parseInput_canonical_candidate

/--
info: 'SlhDsaSecurity.CanonicalGraph.parseInput_canonical_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.parseInput_canonical_parent

/--
info: 'SlhDsaSecurity.CanonicalGraph.parseInput_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.parseInput_none_iff

/--
info: 'SlhDsaSecurity.CanonicalGraph.parseInput_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.parseInput_sound

/--
info: 'SlhDsaSecurity.CanonicalGraph.structuralValue_equation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.structuralValue_equation

/--
info: 'SlhDsaSecurity.CanonicalGraph.truncate_fullOutput' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.truncate_fullOutput

/--
info: 'SlhDsaSecurity.CanonicalGraph.value_equation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.value_equation

/--
info: 'SlhDsaSecurity.CanonicalGraph.value_merkleChild' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.value_merkleChild

/--
info: 'SlhDsaSecurity.CanonicalGraph.value_merkleNode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.value_merkleNode

/--
info: 'SlhDsaSecurity.CanonicalGraph.value_wotsPosition' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.value_wotsPosition

/--
info: 'SlhDsaSecurity.CanonicalGraph.wots_publicKey_cell' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.wots_publicKey_cell

/--
info: 'SlhDsaSecurity.CanonicalTarget.canonicalTarget_deviating' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalTarget.canonicalTarget_deviating

/--
info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_fires' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_fires

/--
info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_neverFails

/--
info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_run

/--
info: 'SlhDsaSecurity.ChargedProbe.sensitiveFlagged_sticky' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ChargedProbe.sensitiveFlagged_sticky

/--
info: 'SlhDsaSecurity.Checksum.checksum_eq_digits' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.checksum_eq_digits

/--
info: 'SlhDsaSecurity.Checksum.checksum_le_of_digits_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.checksum_le_of_digits_le

/--
info: 'SlhDsaSecurity.Checksum.encode_checksumDigit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.encode_checksumDigit

/--
info: 'SlhDsaSecurity.Checksum.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.encode_injective

/--
info: 'SlhDsaSecurity.Checksum.encode_messageDigit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.encode_messageDigit

/--
info: 'SlhDsaSecurity.Checksum.eq_of_encode_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.eq_of_encode_le

/--
info: 'SlhDsaSecurity.Checksum.messageDigit_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Checksum.messageDigit_injective

/--
info: 'SlhDsaSecurity.ClassBudget.countClass_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassBudget.countClass_pure

/--
info: 'SlhDsaSecurity.ClassBudget.countClass_query_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassBudget.countClass_query_bind

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.cacheQuery' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.cacheQuery

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.cacheQuery_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.cacheQuery_other

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.mono' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.mono

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.of_cacheQuery_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.of_cacheQuery_other

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.of_growthAtMost' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.of_growthAtMost

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.pos

/--
info: 'SlhDsaSecurity.ClassCharge.GrowthAtMostOn.succ_of_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassCharge.GrowthAtMostOn.succ_of_cacheQuery

/--
info: 'SlhDsaSecurity.ClassExpectation.count_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.count_map_eq

/--
info: 'SlhDsaSecurity.ClassExpectation.event_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.event_map_eq

/--
info: 'SlhDsaSecurity.ClassExpectation.expected_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_mono

/--
info: 'SlhDsaSecurity.ClassExpectation.expected_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.expected_pure

/--
info: 'SlhDsaSecurity.ClassGrowth.classCost_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.classCost_inl

/--
info: 'SlhDsaSecurity.CollisionToDeviating.childBytes_pair' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.childBytes_pair

/--
info: 'SlhDsaSecurity.CollisionToDeviating.childBytes_single' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CollisionToDeviating.childBytes_single

/--
info: 'SlhDsaSecurity.Correctness.Hypertree.rootFromSignature_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Hypertree.rootFromSignature_sign

/--
info: 'SlhDsaSecurity.Correctness.Hypertree.rootFromSignature_signLayers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Hypertree.rootFromSignature_signLayers

/--
info: 'SlhDsaSecurity.Correctness.Hypertree.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Hypertree.verify_sign

/--
info: 'SlhDsaSecurity.Correctness.Merkle.publicKeyFromSignature_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Merkle.publicKeyFromSignature_sign

/--
info: 'SlhDsaSecurity.Correctness.Naturality.derive_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.derive_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.fors_node_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.fors_node_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.fors_secret_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.fors_secret_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.fors_sign_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.fors_sign_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.hypertree_signLayers_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.hypertree_signLayers_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.hypertree_sign_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.hypertree_sign_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.keygenInternal_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.keygenInternal_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.merkle_node_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.merkle_node_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.merkle_sign_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.merkle_sign_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.randomizer_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.randomizer_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.signInternal_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.signInternal_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.sign_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.sign_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.wots_publicKey_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.wots_publicKey_simulate

/--
info: 'SlhDsaSecurity.Correctness.Naturality.wots_sign_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Naturality.wots_sign_simulate

/--
info: 'SlhDsaSecurity.Correctness.Scheme.verifyInternal_signInternal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Scheme.verifyInternal_signInternal

/--
info: 'SlhDsaSecurity.Correctness.Scheme.verify_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Scheme.verify_sign

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.experiment_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.experiment_run

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.invalid_context_probability_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.invalid_context_probability_one

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.roundTrip_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.roundTrip_fixed

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.roundTrip_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.roundTrip_lift

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.roundTrip_probability_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.roundTrip_probability_one

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.roundTrip_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.roundTrip_simulate

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.signAndVerify_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.signAndVerify_simulate

/--
info: 'SlhDsaSecurity.Correctness.SharedROM.valid_context_probability_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.SharedROM.valid_context_probability_one

/--
info: 'SlhDsaSecurity.Correctness.Wots.chain_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Wots.chain_add

/--
info: 'SlhDsaSecurity.Correctness.Wots.publicKeyFromSignature_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.Wots.publicKeyFromSignature_sign

/--
info: 'SlhDsaSecurity.Correctness.div_pow_succ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.div_pow_succ

/--
info: 'SlhDsaSecurity.Correctness.finRange_foldl' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.finRange_foldl

/--
info: 'SlhDsaSecurity.Correctness.foldlM_id' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.foldlM_id

/--
info: 'SlhDsaSecurity.Correctness.offset_div_pow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.offset_div_pow

/--
info: 'SlhDsaSecurity.Correctness.offset_even' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.offset_even

/--
info: 'SlhDsaSecurity.Correctness.parent_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.parent_reconstruction

/--
info: 'SlhDsaSecurity.Correctness.recover_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.recover_path

/--
info: 'SlhDsaSecurity.Correctness.sequenceFin_id' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.sequenceFin_id

/--
info: 'SlhDsaSecurity.Correctness.xor_add_even' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Correctness.xor_add_even

/--
info: 'SlhDsaSecurity.DigestInputDistinct.messageInput_ne_of_request_ne' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestInputDistinct.messageInput_ne_of_request_ne

/--
info: 'SlhDsaSecurity.DigestTape.answers_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_append

/--
info: 'SlhDsaSecurity.DigestTape.answers_getElem' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_getElem

/--
info: 'SlhDsaSecurity.DigestTape.answers_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_length

/--
info: 'SlhDsaSecurity.DigestTape.answers_nil' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_nil

/--
info: 'SlhDsaSecurity.DigestTape.answers_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_prefix

/--
info: 'SlhDsaSecurity.DigestTape.answers_singleton' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.answers_singleton

/--
info: 'SlhDsaSecurity.DigestTape.mem_record_of_cache' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.mem_record_of_cache

/--
info: 'SlhDsaSecurity.DigestTape.mem_support_rom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.mem_support_rom

/--
info: 'SlhDsaSecurity.DigestTape.recordCovered_of_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recordCovered_of_witnesses

/--
info: 'SlhDsaSecurity.DigestTape.recorder_cache_value_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.DigestTape.recorder_cache_value_persists

/--
info: 'SlhDsaSecurity.EligibilityCertificate.coeff_le_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.coeff_le_eval_one

/--
info: 'SlhDsaSecurity.EligibilityCertificate.count_value' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.count_value

/--
info: 'SlhDsaSecurity.EligibilityCertificate.fastPow_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.fastPow_eq

/--
info: 'SlhDsaSecurity.EligibilityCertificate.pow2_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.EligibilityCertificate.pow2_eq

/--
info: 'SlhDsaSecurity.Extraction.BinaryPath.canonical_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.canonical_step

/--
info: 'SlhDsaSecurity.Extraction.BinaryPath.collision_inputs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.collision_inputs

/--
info: 'SlhDsaSecurity.Extraction.BinaryPath.ordered_eq_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.ordered_eq_iff

/--
info: 'SlhDsaSecurity.Extraction.BinaryPath.pairBytes_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.pairBytes_injective

/--
info: 'SlhDsaSecurity.Extraction.BinaryPath.value_eq_fold' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.BinaryPath.value_eq_fold

/--
info: 'SlhDsaSecurity.Extraction.Fors.publicKeyFromSignature_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Fors.publicKeyFromSignature_eq

/--
info: 'SlhDsaSecurity.Extraction.HypertreeChain.honestFold_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.HypertreeChain.honestFold_eq

/--
info: 'SlhDsaSecurity.Extraction.Wots.chain_collision_inputs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Wots.chain_collision_inputs

/--
info: 'SlhDsaSecurity.Extraction.Wots.chain_eq_or_collision' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Wots.chain_eq_or_collision

/--
info: 'SlhDsaSecurity.Extraction.Wots.digestArrayBytes_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Wots.digestArrayBytes_injective

/--
info: 'SlhDsaSecurity.Extraction.Wots.publicKeyFromSignature_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.Wots.publicKeyFromSignature_eq

/--
info: 'SlhDsaSecurity.Extraction.WotsPreimage.chain_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.WotsPreimage.chain_le

/--
info: 'SlhDsaSecurity.Extraction.WotsPreimage.forged_advances_to_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.WotsPreimage.forged_advances_to_signed

/--
info: 'SlhDsaSecurity.Extraction.WotsPreimage.sign_eq_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Extraction.WotsPreimage.sign_eq_chain

/--
info: 'SlhDsaSecurity.ForsAdaptiveTargets.coverage_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.coverage_le_expected

/--
info: 'SlhDsaSecurity.ForsAdaptiveTargets.expectedUses_eq_sum_prob' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.expectedUses_eq_sum_prob

/--
info: 'SlhDsaSecurity.ForsAdaptiveTargets.history_update' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.history_update

/--
info: 'SlhDsaSecurity.ForsAdaptiveTargets.selected_hit_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.selected_hit_factor

/--
info: 'SlhDsaSecurity.ForsAdaptiveTargets.selected_hit_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsAdaptiveTargets.selected_hit_le_expected

/--
info: 'SlhDsaSecurity.ForsConcentration.mul_descFactorial_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.mul_descFactorial_eq

/--
info: 'SlhDsaSecurity.ForsConcentration.poissonLoads_eq_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poissonLoads_eq_mixture

/--
info: 'SlhDsaSecurity.ForsConcentration.poisson_count_tail_extended_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_count_tail_extended_half

/--
info: 'SlhDsaSecurity.ForsConcentration.poisson_count_tail_half' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_count_tail_half

/--
info: 'SlhDsaSecurity.ForsConcentration.poisson_load_tail_sharper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_load_tail_sharper

/--
info: 'SlhDsaSecurity.ForsConcentration.poisson_three_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.poisson_three_moments

/--
info: 'SlhDsaSecurity.ForsConcentration.power_eq_stirling_descFactorial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.power_eq_stirling_descFactorial

/--
info: 'SlhDsaSecurity.ForsConcentration.touchard_fourteen_three' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.touchard_fourteen_three

/--
info: 'SlhDsaSecurity.ForsConcentration.uniformLoads_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniformLoads_monotone

/--
info: 'SlhDsaSecurity.ForsConcentration.uniformLoads_mul_poisson_tail_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniformLoads_mul_poisson_tail_le

/--
info: 'SlhDsaSecurity.ForsConcentration.uniform_load_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniform_load_tail

/--
info: 'SlhDsaSecurity.ForsConcentration.uniform_load_tail_extended' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniform_load_tail_extended

/--
info: 'SlhDsaSecurity.ForsConcentration.uniform_load_tail_extended_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniform_load_tail_extended_of_le

/--
info: 'SlhDsaSecurity.ForsConcentration.uniform_load_tail_sharper_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.uniform_load_tail_sharper_of_le

/--
info: 'SlhDsaSecurity.ForsConcentration.wordCounts_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsConcentration.wordCounts_fiber_card

/--
info: 'SlhDsaSecurity.ForsCoverage.fresh_coverage_le_sharper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverage.fresh_coverage_le_sharper

/--
info: 'SlhDsaSecurity.ForsCoverageTerm.moment_le_of_small_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.moment_le_of_small_support

/--
info: 'SlhDsaSecurity.ForsCoverageTerm.prob_coveredAnswer_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.prob_coveredAnswer_le

/--
info: 'SlhDsaSecurity.ForsCoverageTerm.prob_coveredAnswer_le_sharper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsCoverageTerm.prob_coveredAnswer_le_sharper

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.coordinate_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.coordinate_injective

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.evalDist_groupLeaves_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.evalDist_groupLeaves_uniform

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.evalDist_joinedTape_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.evalDist_joinedTape_uniform

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.evalDist_uniform_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.evalDist_uniform_pair

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.fixed_assignment_prefix_cap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.fixed_assignment_prefix_cap

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.groupLeaves_covered_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.groupLeaves_covered_iff

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.prefix_tape_uniform_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.prefix_tape_uniform_measure

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.uniform_pi_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.uniform_pi_measure

/--
info: 'SlhDsaSecurity.ForsDisclosurePrefix.wordLoads_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosurePrefix.wordLoads_eq_card

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.bad_load_probability_sharper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.bad_load_probability_sharper

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_card_le_loads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_card_le_loads

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_subset

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_update_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.disclosuresExcept_update_self

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.disclosures_card_le_loads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.disclosures_card_le_loads

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.evalDist_instanceWord_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.evalDist_instanceWord_uniform

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.loads_eq_wordLoads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.loads_eq_wordLoads

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.loads_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.loads_probability

/--
info: 'SlhDsaSecurity.ForsDisclosureTape.uniform_prob_eq_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsDisclosureTape.uniform_prob_eq_measure

/--
info: 'SlhDsaSecurity.ForsLeaveOneOut.coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.coverage_le

/--
info: 'SlhDsaSecurity.ForsLeaveOneOut.coverage_le_of_full_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.coverage_le_of_full_cap

/--
info: 'SlhDsaSecurity.ForsLeaveOneOut.independent_tape_coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.independent_tape_coverage_le

/--
info: 'SlhDsaSecurity.ForsLeaveOneOut.selected_local_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsLeaveOneOut.selected_local_hit_le

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.fixed_prefix_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.fixed_prefix_tail

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.independent_count_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.independent_count_tail

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.prefix_covered_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.prefix_covered_probability

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.prefix_instances_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.prefix_instances_independent

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.prefix_probability_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.prefix_probability_sum

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.product_event_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.product_event_probability

/--
info: 'SlhDsaSecurity.ForsPrefixCapacity.tree_covered_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsPrefixCapacity.tree_covered_probability

/--
info: 'SlhDsaSecurity.ForsTreeSignature.ext' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsTreeSignature.ext

/--
info: 'SlhDsaSecurity.ForsTreeSignature.toBytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ForsTreeSignature.toBytes_length

/--
info: 'SlhDsaSecurity.FramingClosure.chainFrame_eq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_eq_iff

/--
info: 'SlhDsaSecurity.FramingClosure.chainFrame_exists_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_exists_frame

/--
info: 'SlhDsaSecurity.FramingClosure.chainFrame_injective' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_injective

/--
info: 'SlhDsaSecurity.FramingClosure.chainFrame_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_length

/--
info: 'SlhDsaSecurity.FramingClosure.chainFrame_length_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.chainFrame_length_bounds

/--
info: 'SlhDsaSecurity.FramingClosure.digest_bytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.digest_bytes_length

/--
info: 'SlhDsaSecurity.FramingClosure.digest_head_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.digest_head_zero

/--
info: 'SlhDsaSecurity.FramingClosure.exists_frame_of_head_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingClosure.exists_frame_of_head_zero

/--
info: 'SlhDsaSecurity.FramingLeak.chainFrame_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.chainFrame_legal

/--
info: 'SlhDsaSecurity.FramingLeak.chainFrame_randomizer_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.chainFrame_randomizer_eq

/--
info: 'SlhDsaSecurity.FramingLeak.exists_legal_request' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.exists_legal_request

/--
info: 'SlhDsaSecurity.FramingLeak.randomizerInput_eq_messageInput' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingLeak.randomizerInput_eq_messageInput

/--
info: 'SlhDsaSecurity.FramingOverlap.bytesBE_head' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.bytesBE_head

/--
info: 'SlhDsaSecurity.FramingOverlap.firstByte_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.firstByte_uniform

/--
info: 'SlhDsaSecurity.FramingOverlap.frame_head' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.frame_head

/--
info: 'SlhDsaSecurity.FramingOverlap.overlap_requires_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.overlap_requires_zero

/--
info: 'SlhDsaSecurity.FramingOverlap.splitRoot_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.splitRoot_bijective

/--
info: 'SlhDsaSecurity.FramingOverlap.uniform_zero_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FramingOverlap.uniform_zero_probability

/--
info: 'SlhDsaSecurity.FreshDigest.fresh_hash_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.fresh_hash_uniform

/--
info: 'SlhDsaSecurity.FreshDigest.fresh_shortHash_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.fresh_shortHash_uniform

/--
info: 'SlhDsaSecurity.FreshDigest.instanceOf_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.instanceOf_uniform

/--
info: 'SlhDsaSecurity.FreshDigest.splitInstance_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.splitInstance_bijective

/--
info: 'SlhDsaSecurity.FreshDigest.viewAssignment_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshDigest.viewAssignment_uniform

/--
info: 'SlhDsaSecurity.FreshHitBound.Clean.cacheQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshHitBound.Clean.cacheQuery

/--
info: 'SlhDsaSecurity.FreshHitBound.prob_target_match_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshHitBound.prob_target_match_le

/--
info: 'SlhDsaSecurity.FreshHitBound.prob_truncate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.FreshHitBound.prob_truncate_eq

/--
info: 'SlhDsaSecurity.GameBridge.keygenInternal_eq_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.keygenInternal_eq_replay

/--
info: 'SlhDsaSecurity.GameBridge.replay_agrees' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GameBridge.replay_agrees

/--
info: 'SlhDsaSecurity.GraphFreshSampling.evalDist_evaluate_eq_uniform_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphFreshSampling.evalDist_evaluate_eq_uniform_program

/--
info: 'SlhDsaSecurity.GraphFreshSampling.evalDist_sample_eq_uniform_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphFreshSampling.evalDist_sample_eq_uniform_program

/--
info: 'SlhDsaSecurity.GraphFreshSampling.evaluate_eq_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphFreshSampling.evaluate_eq_sample

/--
info: 'SlhDsaSecurity.GraphFreshSampling.program_congr' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphFreshSampling.program_congr

/--
info: 'SlhDsaSecurity.GraphFreshSampling.program_update_outside' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphFreshSampling.program_update_outside

/--
info: 'SlhDsaSecurity.GrowthBudget.GrowthAtMost.mono' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.GrowthAtMost.mono

/--
info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_pure

/--
info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_query' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_query

/--
info: 'SlhDsaSecurity.GrowthBudget.countAllHashes_query_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.countAllHashes_query_bind

/--
info: 'SlhDsaSecurity.GrowthBudget.growth_of_cacheQuery' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthBudget.growth_of_cacheQuery

/--
info: 'SlhDsaSecurity.GrowthCharge.CleanBad.cacheQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.CleanBad.cacheQuery

/--
info: 'SlhDsaSecurity.GrowthCharge.GrowthAtMost.cacheQuery' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.GrowthAtMost.cacheQuery

/--
info: 'SlhDsaSecurity.GrowthCharge.GrowthAtMost.pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.GrowthCharge.GrowthAtMost.pos

/--
info: 'SlhDsaSecurity.HashSeparation.bounded_address_has_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.bounded_address_has_prefix

/--
info: 'SlhDsaSecurity.HashSeparation.message_tweakable_overlap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.message_tweakable_overlap

/--
info: 'SlhDsaSecurity.HashSeparation.prob_publicBytes_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.prob_publicBytes_eq_le

/--
info: 'SlhDsaSecurity.HashSeparation.publicBytes_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HashSeparation.publicBytes_injective

/--
info: 'SlhDsaSecurity.Hashing.tweakableInput_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Hashing.tweakableInput_injective

/--
info: 'SlhDsaSecurity.HypertreeDispatch.queriesUnder_rootFromSignature_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.HypertreeDispatch.queriesUnder_rootFromSignature_head

/--
info: 'SlhDsaSecurity.KeygenUniform.cache_none_of_zero_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.cache_none_of_zero_query_bound

/--
info: 'SlhDsaSecurity.KeygenUniform.chain_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.chain_avoids_root

/--
info: 'SlhDsaSecurity.KeygenUniform.evalDist_bind_eq_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.evalDist_bind_eq_of_support

/--
info: 'SlhDsaSecurity.KeygenUniform.fresh_tweakable_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.fresh_tweakable_uniform

/--
info: 'SlhDsaSecurity.KeygenUniform.keygenInternal_publicPair_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.keygenInternal_publicPair_uniform

/--
info: 'SlhDsaSecurity.KeygenUniform.keygen_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.keygen_run

/--
info: 'SlhDsaSecurity.KeygenUniform.node_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.node_avoids_root

/--
info: 'SlhDsaSecurity.KeygenUniform.sequenceFin_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.sequenceFin_avoids_root

/--
info: 'SlhDsaSecurity.KeygenUniform.splitOutput_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.splitOutput_bijective

/--
info: 'SlhDsaSecurity.KeygenUniform.topChildren_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.topChildren_avoids_root

/--
info: 'SlhDsaSecurity.KeygenUniform.topChildren_root_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.topChildren_root_fresh

/--
info: 'SlhDsaSecurity.KeygenUniform.top_root_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.top_root_uniform

/--
info: 'SlhDsaSecurity.KeygenUniform.truncate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.truncate_uniform

/--
info: 'SlhDsaSecurity.KeygenUniform.tweakable_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.tweakable_avoids_root

/--
info: 'SlhDsaSecurity.KeygenUniform.wots_avoids_root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.KeygenUniform.wots_avoids_root

/--
info: 'SlhDsaSecurity.LazyBudget.lazyProgram_hash_mem_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.lazyProgram_hash_mem_randomOracle

/--
info: 'SlhDsaSecurity.LazyBudget.lazyProgram_run_hash' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.lazyProgram_run_hash

/--
info: 'SlhDsaSecurity.LazyBudget.lazyProgram_step_mem_rom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.LazyBudget.lazyProgram_step_mem_rom

/--
info: 'SlhDsaSecurity.Message.frame_eq_none_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Message.frame_eq_none_iff

/--
info: 'SlhDsaSecurity.MessageDigest.split_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.MessageDigest.split_injective

/--
info: 'SlhDsaSecurity.PartialDigest.coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.coverage_le

/--
info: 'SlhDsaSecurity.PartialDigest.coverage_singleton_le_256' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.coverage_singleton_le_256

/--
info: 'SlhDsaSecurity.PartialDigest.covered_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.covered_card_le

/--
info: 'SlhDsaSecurity.PartialDigest.evalDist_restrict_parse_append_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.evalDist_restrict_parse_append_uniform

/--
info: 'SlhDsaSecurity.PartialDigest.restrict_parse_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.restrict_parse_append

/--
info: 'SlhDsaSecurity.PartialDigest.split_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.split_bijective

/--
info: 'SlhDsaSecurity.PartialDigest.split_injective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.split_injective

/--
info: 'SlhDsaSecurity.PartialDigest.truncate_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.truncate_append

/--
info: 'SlhDsaSecurity.PartialDigest.uniform_coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PartialDigest.uniform_coverage_le

/--
info: 'SlhDsaSecurity.PathEntry.replayFold_eq_value' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PathEntry.replayFold_eq_value

/--
info: 'SlhDsaSecurity.PerQueryBudget.classRate_structural' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.classRate_structural

/--
info: 'SlhDsaSecurity.PerQueryBudget.dearest_within_target' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.dearest_within_target

/--
info: 'SlhDsaSecurity.PerQueryBudget.seedGuessRate_128' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.seedGuessRate_128

/--
info: 'SlhDsaSecurity.PerQueryBudget.seedGuessRate_256' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.seedGuessRate_256

/--
info: 'SlhDsaSecurity.PerQueryBudget.union_bound_is_weaker' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.union_bound_is_weaker

/--
info: 'SlhDsaSecurity.PerQueryBudget.union_rate_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PerQueryBudget.union_rate_eq

/--
info: 'SlhDsaSecurity.Presample.cacheQuery_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.cacheQuery_comm

/--
info: 'SlhDsaSecurity.Presample.countAllHashes_liftM_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Presample.countAllHashes_liftM_bind

/--
info: 'SlhDsaSecurity.QueryCached.step_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.QueryCached.step_cached

/--
info: 'SlhDsaSecurity.ROMPresampling.cacheQuery_comm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.cacheQuery_comm

/--
info: 'SlhDsaSecurity.ROMPresampling.evalDist_presample_computation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.evalDist_presample_computation

/--
info: 'SlhDsaSecurity.ROMPresampling.evalDist_presample_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.evalDist_presample_fresh

/--
info: 'SlhDsaSecurity.ROMPresampling.evalDist_presample_query' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.evalDist_presample_query

/--
info: 'SlhDsaSecurity.ROMPresampling.property_after_preparation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.property_after_preparation

/--
info: 'SlhDsaSecurity.ROMPresampling.run'_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ROMPresampling.run'_query_bind

/--
info: 'SlhDsaSecurity.RecordedBudget.work_add_pow_add_served_le_of_budget_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedBudget.work_add_pow_add_served_le_of_budget_recorded

/--
info: 'SlhDsaSecurity.RedrawCell.unionCache_of_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_of_none

/--
info: 'SlhDsaSecurity.RedrawCell.unionCache_of_open' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_of_open

/--
info: 'SlhDsaSecurity.SecretGuessCharge.prob_either_secret_guessed_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SecretGuessCharge.prob_either_secret_guessed_le

/--
info: 'SlhDsaSecurity.SecretGuessCharge.prob_single_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SecretGuessCharge.prob_single_guess

/--
info: 'SlhDsaSecurity.Security.advantage_standard_le_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.advantage_standard_le_strong

/--
info: 'SlhDsaSecurity.Security.fresh_standard_implies_strong' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.fresh_standard_implies_strong

/--
info: 'SlhDsaSecurity.Security.fst_map_countAllHashes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.fst_map_countAllHashes

/--
info: 'SlhDsaSecurity.Security.fst_map_runAll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.fst_map_runAll

/--
info: 'SlhDsaSecurity.Security.totalAdvantage_standard_le_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Security.totalAdvantage_standard_le_strong

/--
info: 'SlhDsaSecurity.SeedDeferral.sample_fst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.sample_fst_eq

/--
info: 'SlhDsaSecurity.SeedDeferral.seed_query_comm_transcript' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.seed_query_comm_transcript

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.admissible_checksum_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.admissible_checksum_tail

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.baseline_setup_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.baseline_setup_cap

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.continuation_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.continuation_certificate

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.eligible_key_failure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.eligible_key_failure

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.maximum_frame_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.maximum_frame_length

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.occupied_mean_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.occupied_mean_certificate

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.signing_allowance' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.signing_allowance

/--
info: 'SlhDsaSecurity.SharedOracleArithmetic.total_work_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedOracleArithmetic.total_work_cap

/--
info: 'SlhDsaSecurity.Signature.card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.card

/--
info: 'SlhDsaSecurity.Signature.encodeFixed_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.encodeFixed_bijective

/--
info: 'SlhDsaSecurity.Signature.encodeFixed_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.encodeFixed_injective

/--
info: 'SlhDsaSecurity.Signature.readDigest_append_prefix' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_append_prefix

/--
info: 'SlhDsaSecurity.Signature.readDigest_append_suffix' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_append_suffix

/--
info: 'SlhDsaSecurity.Signature.readDigest_bytesBE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_bytesBE

/--
info: 'SlhDsaSecurity.Signature.readDigest_digestArray' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_digestArray

/--
info: 'SlhDsaSecurity.Signature.readDigest_field' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_field

/--
info: 'SlhDsaSecurity.Signature.readDigest_flatten' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_flatten

/--
info: 'SlhDsaSecurity.Signature.readDigest_fors' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_fors

/--
info: 'SlhDsaSecurity.Signature.readDigest_fors_auth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_fors_auth

/--
info: 'SlhDsaSecurity.Signature.readDigest_fors_secret' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_fors_secret

/--
info: 'SlhDsaSecurity.Signature.readDigest_hypertree' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_hypertree

/--
info: 'SlhDsaSecurity.Signature.readDigest_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_randomizer

/--
info: 'SlhDsaSecurity.Signature.readDigest_wots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_wots

/--
info: 'SlhDsaSecurity.Signature.readDigest_xmss_auth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.readDigest_xmss_auth

/--
info: 'SlhDsaSecurity.Signature.toBytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Signature.toBytes_length

/--
info: 'SlhDsaSecurity.SplitRouted.forgedKey_coords' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitRouted.forgedKey_coords

/--
info: 'SlhDsaSecurity.StructuralTerm.prob_hitWithin_canonicalTarget_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.StructuralTerm.prob_hitWithin_canonicalTarget_le

/--
info: 'SlhDsaSecurity.TrackedQueries.meets_persists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.meets_persists

/--
info: 'SlhDsaSecurity.TrackedQueries.subset_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.subset_of_run

/--
info: 'SlhDsaSecurity.TrackedQueries.tracked_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TrackedQueries.tracked_neverFails

/--
info: 'SlhDsaSecurity.VerificationBudget.countQueries_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.countQueries_bind

/--
info: 'SlhDsaSecurity.VerificationBudget.countQueries_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.countQueries_pure

/--
info: 'SlhDsaSecurity.VerificationBudget.countQueries_query' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.countQueries_query

/--
info: 'SlhDsaSecurity.VerificationBudget.counted_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.counted_pure

/--
info: 'SlhDsaSecurity.VerificationBudget.counted_query_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.counted_query_bind

/--
info: 'SlhDsaSecurity.VerificationBudget.verificationCount_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.verificationCount_lift

/--
info: 'SlhDsaSecurity.VerificationBudget.verification_accepted_count_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.verification_accepted_count_bounds

/--
info: 'SlhDsaSecurity.VerificationBudget.verification_count_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.verification_count_bounds

/--
info: 'SlhDsaSecurity.VerificationBudget.verify_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationBudget.verify_lift

/--
info: 'SlhDsaSecurity.VerificationQueries.Bounds.bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.Bounds.bind

/--
info: 'SlhDsaSecurity.VerificationQueries.Bounds.map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.Bounds.map

/--
info: 'SlhDsaSecurity.VerificationQueries.Bounds.mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.Bounds.mono

/--
info: 'SlhDsaSecurity.VerificationQueries.Bounds.of_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.Bounds.of_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.Bounds.simulated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.Bounds.simulated

/--
info: 'SlhDsaSecurity.VerificationQueries.chain_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.chain_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.encoded_chain_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.encoded_chain_steps

/--
info: 'SlhDsaSecurity.VerificationQueries.exact_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.exact_bind

/--
info: 'SlhDsaSecurity.VerificationQueries.exact_cost' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.exact_cost

/--
info: 'SlhDsaSecurity.VerificationQueries.exact_map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.exact_map

/--
info: 'SlhDsaSecurity.VerificationQueries.foldlM_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.foldlM_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.fors_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.fors_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.hash_exact' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.hash_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.hypertree_root_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.hypertree_root_bounds

/--
info: 'SlhDsaSecurity.VerificationQueries.merkle_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.merkle_bounds

/--
info: 'SlhDsaSecurity.VerificationQueries.sequenceFin_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.sequenceFin_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.shortHash_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.shortHash_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.tweakable_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.tweakable_exact

/--
info: 'SlhDsaSecurity.VerificationQueries.verify_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.verify_bounds

/--
info: 'SlhDsaSecurity.VerificationQueries.verify_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.verify_upper

/--
info: 'SlhDsaSecurity.VerificationQueries.wots_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerificationQueries.wots_exact

/--
info: 'SlhDsaSecurity.VerifierNaturality.chain_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.chain_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.foldlM_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.foldlM_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.fors_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.fors_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.hash_simulate' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.hash_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.hypertree_root_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.hypertree_root_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.hypertree_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.hypertree_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.merkle_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.merkle_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.sequenceFin_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.sequenceFin_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.tweakable_simulate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.tweakable_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.verifyInternal_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.verifyInternal_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.verify_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.verify_simulate

/--
info: 'SlhDsaSecurity.VerifierNaturality.wots_simulate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierNaturality.wots_simulate

/--
info: 'SlhDsaSecurity.WarmProbes.lazyProgram_hash_probes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.lazyProgram_hash_probes

/--
info: 'SlhDsaSecurity.WarmProbes.length_warmProbes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.length_warmProbes

/--
info: 'SlhDsaSecurity.WarmProbes.mem_warmProbes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.mem_warmProbes

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_adversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_adversaryImpl

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_append' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_append

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_cold_query_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_cold_query_bind

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_hash_cold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_hash_cold

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_hash_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_hash_le

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_singleton_cold' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_singleton_cold

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_singleton_le' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_singleton_le

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_step_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_step_le

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_strippedKeygen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_strippedKeygen

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_strippedSign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_strippedSign

/--
info: 'SlhDsaSecurity.WarmProbes.warmCount_strippedSigningOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WarmProbes.warmCount_strippedSigningOracle

/--
info: 'SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.add_of_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.add_of_cacheQuery

/--
info: 'SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.cacheQuery' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.cacheQuery

/--
info: 'SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.mono' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.mono

/--
info: 'SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.WeightedGrowthAtMost.pos

/--
info: 'SlhDsaSecurity.WeightedCharge.countJoint_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.countJoint_pure

/--
info: 'SlhDsaSecurity.WeightedCharge.countJoint_query_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.countJoint_query_bind

/--
info: 'SlhDsaSecurity.WeightedCharge.countWeighted_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.countWeighted_pure

/--
info: 'SlhDsaSecurity.WeightedCharge.countWeighted_query_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WeightedCharge.countWeighted_query_bind

/--
info: 'SlhDsaSecurity.WholeGameStructural.count_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.count_le_of_budget

/--
info: 'SlhDsaSecurity.WholeGameStructural.mem_support_runAll_of_mem_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WholeGameStructural.mem_support_runAll_of_mem_support

/--
info: 'SlhDsaSecurity.WriterState.toStateful_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.WriterState.toStateful_run

/--
info: 'SlhDsaSecurity.XmssSignature.ext' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.XmssSignature.ext

/--
info: 'SlhDsaSecurity.XmssSignature.toBytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.XmssSignature.toBytes_length

/--
info: 'SlhDsaSecurity.digestArrayBytes_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.digestArrayBytes_length

/--
info: 'SlhDsaSecurity.length_bytesBE' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.length_bytesBE

/--
info: 'SlhDsaSecurity.ReplayGate.secretKeyOf_publicKey' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.secretKeyOf_publicKey

/--
info: 'SlhDsaSecurity.ReplayGate.keyOf_seed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.keyOf_seed

/--
info: 'SlhDsaSecurity.ReplayGate.signerRandomised_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.signerRandomised_of_replay

/--
info: 'SlhDsaSecurity.ReplayGate.randomizer_eq_of_replay' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.randomizer_eq_of_replay

/--
info: 'SlhDsaSecurity.ReplayGate.eq_signInternal_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.eq_signInternal_of_replay

/--
info: 'SlhDsaSecurity.ReplayGate.signature_eq_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.signature_eq_of_replay

/--
info: 'SlhDsaSecurity.ReplayGate.randomiserBad_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.randomiserBad_of_replay

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_record_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_record_hit_le

/-- info: 'SlhDsaSecurity.SensitiveQuery.prob_probes_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SensitiveQuery.prob_probes_hit_le

/-- info: 'SlhDsaSecurity.AnswerSide.prob_canonicalBad_message_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_canonicalBad_message_eq_zero

/-- info: 'SlhDsaSecurity.AnswerSide.prob_canonicalBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_canonicalBad_le

/-- info: 'SlhDsaSecurity.AnswerSide.prob_deviatingCollision_outside_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_deviatingCollision_outside_le

/-- info: 'SlhDsaSecurity.AnswerSide.prob_answerBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_answerBad_le

/-- info: 'SlhDsaSecurity.AnswerSide.generatedKey_eq_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.generatedKey_eq_walk

/-- info: 'SlhDsaSecurity.AnswerSide.prob_answerBad_generated_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_answerBad_generated_le

/-- info: 'SlhDsaSecurity.AnswerSide.value_replay_walk_eq_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.value_replay_walk_eq_cells

/-- info: 'SlhDsaSecurity.AnswerSide.generatedKey_eq_walk_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.generatedKey_eq_walk_pair

/-- info: 'SlhDsaSecurity.AnswerSide.not_possible_generatedKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.not_possible_generatedKey

/-- info: 'SlhDsaSecurity.AnswerSide.prob_answerBad_good_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_answerBad_good_le

/-- info: 'SlhDsaSecurity.AnswerSide.prob_answerBad_le_of_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_answerBad_le_of_classes

/--
info: 'SlhDsaSecurity.ReplayGate.cases_of_win_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ReplayGate.cases_of_win_charged

/-- info: 'SlhDsaSecurity.RedrawCell.replayCells_unionCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.replayCells_unionCache

/-- info: 'SlhDsaSecurity.RedrawCell.forsTreeSignature_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.forsTreeSignature_eq

/-- info: 'SlhDsaSecurity.RedrawCell.fors_sign_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.fors_sign_congr

/--
info: 'SlhDsaSecurity.Obligations.target_of_charges' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Obligations.target_of_charges

/--
info: 'SlhDsaSecurity.RandomiserCharge.walk_cache_prf_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.walk_cache_prf_fresh

/-- info: 'SlhDsaSecurity.GraphStakes.available_wotsPosition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.available_wotsPosition

/-- info: 'SlhDsaSecurity.CoverageRouted.forgeryDisclosedCovered_or_only_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.forgeryDisclosedCovered_or_only_self

/-- info: 'SlhDsaSecurity.CoverageRouted.forgeryCovered_of_disclosed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.forgeryCovered_of_disclosed

/-- info: 'SlhDsaSecurity.CoverageRouted.forgeryDisclosedCovered_of_witnesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CoverageRouted.forgeryDisclosedCovered_of_witnesses

/--
info: 'SlhDsaSecurity.VerifierFormat.tweakableAt_input' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.tweakableAt_input

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_chain' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_chain

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_wots_fromSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_wots_fromSignature

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_merkle_fromSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_merkle_fromSignature

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_fors_fromSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_fors_fromSignature

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_rootFromSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_rootFromSignature

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_hypertree_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_hypertree_verify

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_verifyInternal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_verifyInternal

/--
info: 'SlhDsaSecurity.VerifierFormat.probes_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.probes_verify

/--
info: 'SlhDsaSecurity.VerifierFormat.verify_probe_randomizerInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.VerifierFormat.verify_probe_randomizerInput

/-- info: 'SlhDsaSecurity.GraphStakes.honestMessage_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.honestMessage_succ

/--
info: 'SlhDsaSecurity.RandomiserCharge.queriesUnder_of_strip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.queriesUnder_of_strip

/--
info: 'SlhDsaSecurity.RandomiserCharge.keygen_probe_ne_randomizerInput' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.keygen_probe_ne_randomizerInput

/--
info: 'SlhDsaSecurity.RandomiserCharge.sign_probe_messageProbe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.sign_probe_messageProbe

/--
info: 'SlhDsaSecurity.RandomiserCharge.honest_probe_randomizerInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.honest_probe_randomizerInput

/--
info: 'SlhDsaSecurity.SigningFaithful.FaithfulFrom.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.FaithfulFrom.mono

/--
info: 'SlhDsaSecurity.SigningFaithful.faithfulFrom_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.faithfulFrom_nil

/--
info: 'SlhDsaSecurity.SigningFaithful.FaithfulFrom.append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.FaithfulFrom.append

/--
info: 'SlhDsaSecurity.SigningFaithful.sign_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.sign_eq_map

/--
info: 'SlhDsaSecurity.SigningFaithful.sign_replay_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.sign_replay_eq

/--
info: 'SlhDsaSecurity.SigningFaithful.faithfulFrom_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.faithfulFrom_sign

/--
info: 'SlhDsaSecurity.SigningFaithful.faithfulFrom_adversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.faithfulFrom_adversaryImpl

/--
info: 'SlhDsaSecurity.SigningFaithful.faithfulFrom_signingOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.faithfulFrom_signingOracle

/--
info: 'SlhDsaSecurity.SigningFaithful.faithfulFrom_countedRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.faithfulFrom_countedRun

/--
info: 'SlhDsaSecurity.SigningFaithful.length_le_signing_adversaryImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.length_le_signing_adversaryImpl

/--
info: 'SlhDsaSecurity.SigningFaithful.length_le_signing_signingOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.length_le_signing_signingOracle

/--
info: 'SlhDsaSecurity.SigningFaithful.length_le_signing_countedRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.length_le_signing_countedRun

/--
info: 'SlhDsaSecurity.SigningFaithful.signing_countQueries_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.signing_countQueries_eq_zero

/--
info: 'SlhDsaSecurity.SigningFaithful.verifierCost_signing' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.verifierCost_signing

/--
info: 'SlhDsaSecurity.SigningFaithful.keygen_secretKey' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.keygen_secretKey

/--
info: 'SlhDsaSecurity.SigningFaithful.split_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.split_phase

/--
info: 'SlhDsaSecurity.SigningFaithful.logFaithful_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.logFaithful_tail

/--
info: 'SlhDsaSecurity.SigningFaithful.signed_length_le_signing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.signed_length_le_signing

/--
info: 'SlhDsaSecurity.SigningFaithful.signed_length_le_signing_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.signed_length_le_signing_tail

/--
info: 'SlhDsaSecurity.SigningFaithful.cases_of_win_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SigningFaithful.cases_of_win_charged

/--
info: 'SlhDsaSecurity.RandomiserCharge.randomizerIndex_input' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.randomizerIndex_input

/--
info: 'SlhDsaSecurity.RandomiserCharge.randomizerInput_injective_prf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserCharge.randomizerInput_injective_prf

/-- info: 'SlhDsaSecurity.CanonicalGraph.alwaysAvailable_merkleNode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.CanonicalGraph.alwaysAvailable_merkleNode

/-- info: 'SlhDsaSecurity.RedrawCell.xmssSignature_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.xmssSignature_eq

/-- info: 'SlhDsaSecurity.RedrawCell.signLayers_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signLayers_congr

/-- info: 'SlhDsaSecurity.BlockDisclosures.evalDist_leftTape_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.evalDist_leftTape_uniform

/-- info: 'SlhDsaSecurity.BlockDisclosures.block_bad_load_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.block_bad_load_probability

/-- info: 'SlhDsaSecurity.BlockDisclosures.blockDisclosuresExcept_card_le_loads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.blockDisclosuresExcept_card_le_loads

/-- info: 'SlhDsaSecurity.BlockDisclosures.blockDisclosuresExcept_update_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.blockDisclosuresExcept_update_self

/-- info: 'SlhDsaSecurity.BlockDisclosures.block_coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.block_coverage_le

/-- info: 'SlhDsaSecurity.BlockDisclosures.uses_le_of_declines_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.uses_le_of_declines_block

/-- info: 'SlhDsaSecurity.BlockDisclosures.expectedUses_le_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.expectedUses_le_trials

/-- info: 'SlhDsaSecurity.BlockDisclosures.block_coverage_le_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.block_coverage_le_trials

/-- info: 'SlhDsaSecurity.RoutedSplit.selfRandomised_of_only_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RoutedSplit.selfRandomised_of_only_self

/--
info: 'SlhDsaSecurity.BlockDisclosures.splitBlocks_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockDisclosures.splitBlocks_fst

/-- info: 'SlhDsaSecurity.GraphStakes.honestMessage_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.GraphStakes.honestMessage_zero

/-- info: 'SlhDsaSecurity.OpenCache.openCache_eq_none_of_not_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.OpenCache.openCache_eq_none_of_not_canonical

/-- info: 'SlhDsaSecurity.RedrawCell.unionCache_of_not_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.unionCache_of_not_canonical

/--
info: 'SlhDsaSecurity.ClassGrowth.splitCost_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.splitCost_inl

/--
info: 'SlhDsaSecurity.ClassGrowth.splitCost_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.splitCost_inside

/--
info: 'SlhDsaSecurity.ClassGrowth.splitCost_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.splitCost_outside

/--
info: 'SlhDsaSecurity.ClassGrowth.splitCost_add_eq_hashCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.splitCost_add_eq_hashCost

/--
info: 'SlhDsaSecurity.ClassGrowth.growthOn_step_of_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_step_of_charge

/--
info: 'SlhDsaSecurity.ClassGrowth.growthOn_le_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_le_count

/--
info: 'SlhDsaSecurity.ClassGrowth.growthOn_le_splitCount_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_le_splitCount_inside

/--
info: 'SlhDsaSecurity.ClassGrowth.growthOn_le_splitCount_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.growthOn_le_splitCount_outside

/--
info: 'SlhDsaSecurity.ClassGrowth.countAllHashes_eq_readOff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.countAllHashes_eq_readOff

/--
info: 'SlhDsaSecurity.ClassGrowth.run_countQueries_eq_map_readOff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.run_countQueries_eq_map_readOff

/--
info: 'SlhDsaSecurity.ClassGrowth.splitSum_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.splitSum_add

/--
info: 'SlhDsaSecurity.ClassGrowth.run_splitCost_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.run_splitCost_eq_map

/--
info: 'SlhDsaSecurity.ClassGrowth.probEvent_splitCost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.probEvent_splitCost

/--
info: 'SlhDsaSecurity.ClassGrowth.mem_support_countAllHashes_of_splitCost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassGrowth.mem_support_countAllHashes_of_splitCost

/--
info: 'SlhDsaSecurity.ClassExpectation.count_map_eq_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.count_map_eq_slot

/--
info: 'SlhDsaSecurity.ClassExpectation.prob_bad_le_expected_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.prob_bad_le_expected_cost

/--
info: 'SlhDsaSecurity.ClassExpectation.add_le_of_shared_budget_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.add_le_of_shared_budget_const

/--
info: 'SlhDsaSecurity.ClassExpectation.prob_bad_le_expected_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.prob_bad_le_expected_outside

/--
info: 'SlhDsaSecurity.ClassExpectation.prob_bad_or_coverage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.ClassExpectation.prob_bad_or_coverage_le

/--
info: 'SlhDsaSecurity.AnswerSide.prob_answerBad_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.AnswerSide.prob_answerBad_le_of_budget

/-- info: 'SlhDsaSecurity.SplitPrefix.left_prefix_appended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.left_prefix_appended

/-- info: 'SlhDsaSecurity.SplitPrefix.right_prefix_appended' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.right_prefix_appended

/-- info: 'SlhDsaSecurity.SplitPrefix.record_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.record_prefix

/-- info: 'SlhDsaSecurity.SplitPrefix.record_prefix_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.record_prefix_padded

/-- info: 'SlhDsaSecurity.SplitPrefix.prob_and_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.prob_and_bind_le

/-- info: 'SlhDsaSecurity.SplitPrefix.eq_head_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.eq_head_of_prefix

/-- info: 'SlhDsaSecurity.SplitPrefix.prob_prefix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.prob_prefix_le

/--
info: 'SlhDsaSecurity.Assembly.le_target_of_full' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Assembly.le_target_of_full

/--
info: 'SlhDsaSecurity.SplitPrefix.recorder_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.recorder_run_inl

/--
info: 'SlhDsaSecurity.SplitPrefix.recorder_run_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.recorder_run_inr

/--
info: 'SlhDsaSecurity.SplitPrefix.paddedFrom_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.paddedFrom_bind

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_liftM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_liftM

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_liftComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_liftComp

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_keygenInternal_of_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_keygenInternal_of_fresh

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_sign_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_sign_of_fresh

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_verify_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_verify_of_fresh

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_of_fresh_subset

/--
info: 'SlhDsaSecurity.CacheProvenance.queried_of_fresh_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queried_of_fresh_step

/--
info: 'SlhDsaSecurity.PhaseProvenance.recordedRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.recordedRun_bind

/--
info: 'SlhDsaSecurity.PhaseProvenance.persists_of_mem_recordedRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.persists_of_mem_recordedRun

/--
info: 'SlhDsaSecurity.PhaseProvenance.log_eq_recordedAdversaryImpl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.log_eq_recordedAdversaryImpl

/--
info: 'SlhDsaSecurity.PhaseProvenance.log_eq_recordedSigningOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.log_eq_recordedSigningOracle

/--
info: 'SlhDsaSecurity.PhaseProvenance.log_append' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.log_append

/--
info: 'SlhDsaSecurity.PhaseProvenance.mem_record_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.mem_record_of_fresh

/--
info: 'SlhDsaSecurity.PhaseProvenance.provenance_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.provenance_phase

/--
info: 'SlhDsaSecurity.PhaseProvenance.exists_recorded_of_mem_countedRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.exists_recorded_of_mem_countedRun

/--
info: 'SlhDsaSecurity.PhaseProvenance.provenance_phase_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.provenance_phase_subset

/--
info: 'SlhDsaSecurity.RandomiserProvenance.keygen_not_randomizerInput' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.keygen_not_randomizerInput

/--
info: 'SlhDsaSecurity.RandomiserProvenance.sign_messageProbe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.sign_messageProbe

/--
info: 'SlhDsaSecurity.RandomiserProvenance.provenance_afterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.provenance_afterSeeds

/--
info: 'SlhDsaSecurity.RandomiserProvenance.randomiserBad_source' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.randomiserBad_source

/-- info: 'SlhDsaSecurity.RedrawCell.randomizer_replay' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.randomizer_replay

/-- info: 'SlhDsaSecurity.RedrawCell.messageDigest_replay' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.messageDigest_replay

/-- info: 'SlhDsaSecurity.RedrawCell.signedDigest_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signedDigest_congr

/-- info: 'SlhDsaSecurity.RedrawCell.fors_sign_congr_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.fors_sign_congr_shared

/-- info: 'SlhDsaSecurity.RedrawCell.signLayers_congr_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signLayers_congr_shared

/-- info: 'SlhDsaSecurity.SplitPrefix.appended_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.appended_of_cached

/-- info: 'SlhDsaSecurity.SplitPrefix.appended_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.appended_of_left

/-- info: 'SlhDsaSecurity.SplitPrefix.appended_of_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.appended_of_right

/-- info: 'SlhDsaSecurity.SplitPrefix.appended_of_neither' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.appended_of_neither

/-- info: 'SlhDsaSecurity.SplitPrefix.recorder_eq_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.recorder_eq_rom

/-- info: 'SlhDsaSecurity.SplitPrefix.mem_support_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.mem_support_rom

/-- info: 'SlhDsaSecurity.SplitPrefix.recorder_cache_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.recorder_cache_mono

/-- info: 'SlhDsaSecurity.SplitPrefix.recorder_cache_value_persists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.recorder_cache_value_persists

/-- info: 'SlhDsaSecurity.SplitPrefix.mem_record_of_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.mem_record_of_cache

/-- info: 'SlhDsaSecurity.SplitPrefix.growthOn_cacheQuery' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.growthOn_cacheQuery

/-- info: 'SlhDsaSecurity.SplitPrefix.left_record_length_le_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.left_record_length_le_growth

/-- info: 'SlhDsaSecurity.SplitPrefix.right_record_length_le_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.right_record_length_le_growth

/-- info: 'SlhDsaSecurity.SplitPrefix.left_record_keep_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.left_record_keep_final

/-- info: 'SlhDsaSecurity.SplitPrefix.right_record_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.right_record_class

/-- info: 'SlhDsaSecurity.SplitWitness.cover_messageInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.cover_messageInput

/-- info: 'SlhDsaSecurity.SplitWitness.disclosingKeep_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.disclosingKeep_mono

/-- info: 'SlhDsaSecurity.SplitWitness.targetKeep_class' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.targetKeep_class

/-- info: 'SlhDsaSecurity.SplitWitness.disclosingKeep_class' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.disclosingKeep_class

/-- info: 'SlhDsaSecurity.SplitWitness.mem_records_of_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.mem_records_of_covered

/-- info: 'SlhDsaSecurity.RedrawCell.signature_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signature_eq

/-- info: 'SlhDsaSecurity.RedrawCell.randomizer_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.randomizer_congr

/-- info: 'SlhDsaSecurity.SplitPrefix.right_record_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitPrefix.right_record_witness

/-- info: 'SlhDsaSecurity.SplitWitness.disclosedRecorded_of_not_late' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.disclosedRecorded_of_not_late

/-- info: 'SlhDsaSecurity.SplitWitness.late_ordering' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.late_ordering

/-- info: 'SlhDsaSecurity.SplitWitness.mem_records_of_covered_of_not_late' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.mem_records_of_covered_of_not_late

/-- info: 'SlhDsaSecurity.RandomiserDeferral.withPrf_prf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.withPrf_prf

/--
info: 'SlhDsaSecurity.RandomiserDeferral.mem_support_withPrf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.mem_support_withPrf

/-- info: 'SlhDsaSecurity.RandomiserDeferral.goodWalk_withPrf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.goodWalk_withPrf

/--
info: 'SlhDsaSecurity.RandomiserDeferral.graphWalk_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.graphWalk_expand

/--
info: 'SlhDsaSecurity.RandomiserDeferral.evalDist_graphWalk_late' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.evalDist_graphWalk_late

/--
info: 'SlhDsaSecurity.RandomiserDeferral.evalDist_resample_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.evalDist_resample_prf

/--
info: 'SlhDsaSecurity.RandomiserDeferral.probEvent_bind_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.probEvent_bind_le

/--
info: 'SlhDsaSecurity.RandomiserDeferral.probEvent_le_of_prfTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.probEvent_le_of_prfTail

/-- info: 'SlhDsaSecurity.RandomiserDeferral.prob_record_meets_prfClass_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserDeferral.prob_record_meets_prfClass_le

/--
info: 'SlhDsaSecurity.RecordedTail.map_recordedAfterSeeds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.map_recordedAfterSeeds

/--
info: 'SlhDsaSecurity.RecordedTail.card_eq_work' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.card_eq_work

/--
info: 'SlhDsaSecurity.RecordedTail.card_toFinset_le_work' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.card_toFinset_le_work

/--
info: 'SlhDsaSecurity.RecordedTail.countAllHashes_map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.countAllHashes_map

/--
info: 'SlhDsaSecurity.RecordedTail.tail_eq_map_recordedTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.tail_eq_map_recordedTail

/--
info: 'SlhDsaSecurity.RecordedTail.mem_support_tail_of_recorded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.mem_support_tail_of_recorded

/--
info: 'SlhDsaSecurity.RecordedTail.card_toFinset_le_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.card_toFinset_le_count

/--
info: 'SlhDsaSecurity.RecordedTail.probEvent_tail_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RecordedTail.probEvent_tail_eq

/--
info: 'SlhDsaSecurity.CacheProvenance.queriesUnder_sign_randomizer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.queriesUnder_sign_randomizer

/--
info: 'SlhDsaSecurity.CacheProvenance.sign_randomizer_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.CacheProvenance.sign_randomizer_cached

/--
info: 'SlhDsaSecurity.PhaseProvenance.signerMade_of_fresh_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.PhaseProvenance.signerMade_of_fresh_step

/--
info: 'SlhDsaSecurity.RandomiserProvenance.bad_of_signerHitsSeed' does not depend on any axioms
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.bad_of_signerHitsSeed

/--
info: 'SlhDsaSecurity.RandomiserProvenance.card_forgeryDigestRecord_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.card_forgeryDigestRecord_le

/--
info: 'SlhDsaSecurity.RandomiserProvenance.mem_forgeryDigestRecord' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.mem_forgeryDigestRecord

/--
info: 'SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_tail_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_tail_le

/-- info: 'SlhDsaSecurity.RedrawCell.value_unionCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.value_unionCache

/-- info: 'SlhDsaSecurity.RedrawCell.forsKey_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.forsKey_congr

/-- info: 'SlhDsaSecurity.RedrawCell.signature_mk_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signature_mk_eq

/--
info: 'SlhDsaSecurity.Target.prob_bad_walk_paired' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.Target.prob_bad_walk_paired

/-- info: 'SlhDsaSecurity.LateCharge.prob_truncate_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.prob_truncate_mem_le

/-- info: 'SlhDsaSecurity.LateCharge.spent_of_signerRandomised' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.spent_of_signerRandomised

/-- info: 'SlhDsaSecurity.LateCharge.spent_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.spent_mono

/-- info: 'SlhDsaSecurity.LateCharge.not_signerRandomised_of_spent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.not_signerRandomised_of_spent

/-- info: 'SlhDsaSecurity.RedrawCell.forsKeyOf_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.forsKeyOf_eq

/-- info: 'SlhDsaSecurity.RedrawCell.forsRoots_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.forsRoots_key

/-- info: 'SlhDsaSecurity.RedrawCell.signInternal_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.RedrawCell.signInternal_congr

/--
info: 'SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_paired_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_paired_le

/--
info: 'SlhDsaSecurity.TapeFactor.tapeRecorder_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.tapeRecorder_run_inl

/--
info: 'SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_other' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_other

/--
info: 'SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_cons

/--
info: 'SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.tapeRecorder_run_inr_nil

/--
info: 'SlhDsaSecurity.TapeFactor.recorder_run_inr_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.recorder_run_inr_fresh

/--
info: 'SlhDsaSecurity.TapeFactor.recorder_run_inr_other' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.recorder_run_inr_other

/--
info: 'SlhDsaSecurity.TapeFactor.evalDist_tapeRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.evalDist_tapeRun

/--
info: 'SlhDsaSecurity.TapeFactor.padding_zero_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.padding_zero_bind

/--
info: 'SlhDsaSecurity.TapeFactor.padding_succ_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.padding_succ_bind

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_inl

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_left_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_left_cons

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_left_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_left_nil

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_right_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_right_cons

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_right_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_right_nil

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_other' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_run_other

/--
info: 'SlhDsaSecurity.TapeFactor.splitRecorder_run_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitRecorder_run_left

/--
info: 'SlhDsaSecurity.TapeFactor.splitRecorder_run_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitRecorder_run_right

/--
info: 'SlhDsaSecurity.TapeFactor.splitRecorder_run_other' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitRecorder_run_other

/--
info: 'SlhDsaSecurity.TapeFactor.evalDist_comm_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.evalDist_comm_blocks

/--
info: 'SlhDsaSecurity.TapeFactor.evalDist_splitTapeRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.evalDist_splitTapeRun

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRecorder_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRecorder_step

/--
info: 'SlhDsaSecurity.TapeFactor.splitTapeRun_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.splitTapeRun_neverFails

/--
info: 'SlhDsaSecurity.TapeFactor.rightOf_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.rightOf_prefix

/--
info: 'SlhDsaSecurity.TapeFactor.probEvent_length_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.probEvent_length_eq_one

/--
info: 'SlhDsaSecurity.TapeFactor.probEvent_length_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.probEvent_length_set

/--
info: 'SlhDsaSecurity.TapeFactor.evalDist_padding_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.evalDist_padding_set

/--
info: 'SlhDsaSecurity.TapeFactor.eq_of_getElem?_set' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.eq_of_getElem?_set

/--
info: 'SlhDsaSecurity.TapeFactor.probEvent_const_and' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.probEvent_const_and

/--
info: 'SlhDsaSecurity.TapeFactor.prob_selected_hit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.prob_selected_hit_le

/--
info: 'SlhDsaSecurity.TapeFactor.sum_tsum_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.sum_tsum_comm

/--
info: 'SlhDsaSecurity.TapeFactor.sum_prob_selected_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.sum_prob_selected_le_expected

/--
info: 'SlhDsaSecurity.TapeFactor.prob_exists_hit_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.prob_exists_hit_le_expected

/--
info: 'SlhDsaSecurity.TapeFactor.getElem?_of_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.getElem?_of_prefix

/--
info: 'SlhDsaSecurity.TapeFactor.rightOf_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.rightOf_getElem?

/-- info: 'SlhDsaSecurity.PotentialCharge.expected_congr_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PotentialCharge.expected_congr_support

/-- info: 'SlhDsaSecurity.PotentialCharge.tsum_const_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PotentialCharge.tsum_const_add

/-- info: 'SlhDsaSecurity.PotentialCharge.prob_fired_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.PotentialCharge.prob_fired_le

/-- info: 'SlhDsaSecurity.WalkTable.evalDist_bind_congr_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.evalDist_bind_congr_support

/-- info: 'SlhDsaSecurity.WalkTable.cellsOfOutputs_fullOutput' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.cellsOfOutputs_fullOutput

/-- info: 'SlhDsaSecurity.WalkTable.mem_support_graphWalk_walkOfTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.mem_support_graphWalk_walkOfTable

/-- info: 'SlhDsaSecurity.WalkTable.secretSeed_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.secretSeed_of_mem_support

/-- info: 'SlhDsaSecurity.WalkTable.evalDist_warmup_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.evalDist_warmup_table

/-- info: 'SlhDsaSecurity.WalkTable.evalDist_graphWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.evalDist_graphWalk

/-- info: 'SlhDsaSecurity.WalkTable.evalDist_pairedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.evalDist_pairedRun

/-- info: 'SlhDsaSecurity.WalkTable.probEvent_pairedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.probEvent_pairedRun

/-- info: 'SlhDsaSecurity.WalkTable.uniformSample_prod_eq_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.uniformSample_prod_eq_bind

/-- info: 'SlhDsaSecurity.WalkTable.tableRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.tableRun_eq

/-- info: 'SlhDsaSecurity.WalkTable.probEvent_pairedRun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.probEvent_pairedRun_le

/--
info: 'SlhDsaSecurity.RandomiserProvenance.entryCandidates_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.entryCandidates_eq

/--
info: 'SlhDsaSecurity.RandomiserProvenance.card_entryCandidates_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.card_entryCandidates_le

/--
info: 'SlhDsaSecurity.RandomiserProvenance.card_prfCandidates_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.card_prfCandidates_le

/--
info: 'SlhDsaSecurity.RandomiserProvenance.mem_prfCandidates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.mem_prfCandidates

/--
info: 'SlhDsaSecurity.RandomiserProvenance.growthAtMostOn_prfClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.growthAtMostOn_prfClass

/--
info: 'SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_within_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_within_le

/--
info: 'SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_paired_within_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.RandomiserProvenance.prob_signerHitsSeed_paired_within_le

/-- info: 'SlhDsaSecurity.LateCharge.fires_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.fires_shape

/-- info: 'SlhDsaSecurity.LateCharge.prob_entry_fires_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.prob_entry_fires_le

/-- info: 'SlhDsaSecurity.LateCharge.persists_cacheQuery' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.persists_cacheQuery

/-- info: 'SlhDsaSecurity.LateCharge.spent_cacheQuery_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.spent_cacheQuery_iff

/-- info: 'SlhDsaSecurity.LateCharge.prob_record_fires_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateCharge.prob_record_fires_le

/-- info: 'SlhDsaSecurity.LateRate.length_filter_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.length_filter_split

/-- info: 'SlhDsaSecurity.LateRate.fired_iff_lateDisclosure' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.fired_iff_lateDisclosure

/-- info: 'SlhDsaSecurity.LateRate.run_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.run_inl

/-- info: 'SlhDsaSecurity.LateRate.run_inl_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.run_inl_mass

/-- info: 'SlhDsaSecurity.LateRate.run_inr_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.run_inr_cached

/-- info: 'SlhDsaSecurity.LateRate.run_inr_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.run_inr_fresh

/-- info: 'SlhDsaSecurity.LateRate.run_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.run_mass

/-- info: 'SlhDsaSecurity.LateRate.gauge_stepOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.gauge_stepOf

/-- info: 'SlhDsaSecurity.LateRate.gauge_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.gauge_run

/-- info: 'SlhDsaSecurity.LateRate.becomesSpent_of_spent' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.becomesSpent_of_spent

/-- info: 'SlhDsaSecurity.LateRate.potential_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.potential_split

/-- info: 'SlhDsaSecurity.LateRate.potential_stepOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.potential_stepOf

/-- info: 'SlhDsaSecurity.LateRate.rate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.rate_le

/-- info: 'SlhDsaSecurity.LateRate.rate_le3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.rate_le3

/-- info: 'SlhDsaSecurity.LateRate.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.step_bound

/-- info: 'SlhDsaSecurity.LateRate.prob_lateDisclosure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.prob_lateDisclosure_le

/-- info: 'SlhDsaSecurity.WalkTable.probEvent_tableRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.probEvent_tableRun_eq

/-- info: 'SlhDsaSecurity.WalkTable.probEvent_pairedRun_le_of_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.probEvent_pairedRun_le_of_charge

/-- info: 'SlhDsaSecurity.WalkTable.sharedReduced_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.sharedReduced_iff

/-- info: 'SlhDsaSecurity.WalkTable.cacheBlind_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.cacheBlind_shared

/-- info: 'SlhDsaSecurity.WalkTable.probEvent_shared_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.WalkTable.probEvent_shared_le

/-- info: 'SlhDsaSecurity.TableTail.walkOfTable_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.walkOfTable_cache

/-- info: 'SlhDsaSecurity.TableTail.walkOfTable_cache_eq_openCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.walkOfTable_cache_eq_openCache

/-- info: 'SlhDsaSecurity.TableTail.probEvent_tail_uncounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_tail_uncounted

/-- info: 'SlhDsaSecurity.TableTail.probEvent_tail_stripped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_tail_stripped

/-- info: 'SlhDsaSecurity.TableTail.probEvent_tail_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_tail_recorded

/-- info: 'SlhDsaSecurity.TableTail.probEvent_tail_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_tail_linked

/-- info: 'SlhDsaSecurity.TableTail.probEvent_linked_handler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_linked_handler

/-- info: 'SlhDsaSecurity.TableTail.probEvent_tail_handler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.TableTail.probEvent_tail_handler

/-- info: 'SlhDsaSecurity.LateRate.signer_randomizerInput_isMessageInput' depends on axioms: [propext] -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.signer_randomizerInput_isMessageInput

/--
info: 'SlhDsaSecurity.BlockViews.uniformSample_prod_eq_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.uniformSample_prod_eq_bind

/--
info: 'SlhDsaSecurity.BlockViews.cons_bijective' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.cons_bijective

/--
info: 'SlhDsaSecurity.BlockViews.evalDist_padding_eq_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.evalDist_padding_eq_ofFn

/--
info: 'SlhDsaSecurity.BlockViews.evalDist_parse_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.evalDist_parse_uniform

/--
info: 'SlhDsaSecurity.BlockViews.evalDist_blockTape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.evalDist_blockTape

/--
info: 'SlhDsaSecurity.BlockViews.prob_not_goodBlock_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.prob_not_goodBlock_le

/--
info: 'SlhDsaSecurity.BlockViews.prob_blockHit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.prob_blockHit_le

/--
info: 'SlhDsaSecurity.TapeFactor.leftOf_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.leftOf_prefix

/--
info: 'SlhDsaSecurity.TapeFactor.leftOf_getElem?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.TapeFactor.leftOf_getElem?

/--
info: 'SlhDsaSecurity.BlockViews.covered_of_recordCovers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.covered_of_recordCovers

/--
info: 'SlhDsaSecurity.BlockViews.evalDist_recordedRun_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.evalDist_recordedRun_eq

/--
info: 'SlhDsaSecurity.BlockViews.mem_support_blockRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.mem_support_blockRun

/--
info: 'SlhDsaSecurity.BlockViews.blockRun_tail_neverFails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.blockRun_tail_neverFails

/--
info: 'SlhDsaSecurity.BlockViews.prob_leftBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.prob_leftBlock

/--
info: 'SlhDsaSecurity.BlockViews.tsum_probOutput_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.tsum_probOutput_map

/--
info: 'SlhDsaSecurity.BlockViews.prob_targetCovered_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.BlockViews.prob_targetCovered_le

/--
info: 'SlhDsaSecurity.SharedJoin.prob_sharedBad_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.prob_sharedBad_le_sum

/--
info: 'SlhDsaSecurity.SharedJoin.add_rearrange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.add_rearrange

/--
info: 'SlhDsaSecurity.SharedJoin.prob_sharedBad_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.prob_sharedBad_le_expected

/--
info: 'SlhDsaSecurity.SharedJoin.prob_sharedBad_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.prob_sharedBad_le

/--
info: 'SlhDsaSecurity.SharedJoin.prob_signerEvent_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.prob_signerEvent_le

/--
info: 'SlhDsaSecurity.SharedJoin.sharedCharged_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SlhDsaSecurity.SharedJoin.sharedCharged_of_parts

/-- info: 'SlhDsaSecurity.LateRate.not_targetKeep_signer_randomizerInput' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.LateRate.not_targetKeep_signer_randomizerInput

/-- info: 'SlhDsaSecurity.SplitWitness.SeedRandomised' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.SeedRandomised

/-- info: 'SlhDsaSecurity.SplitWitness.not_prfClass_of_not_seedRandomised' does not depend on any axioms -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.not_prfClass_of_not_seedRandomised

/-- info: 'SlhDsaSecurity.SplitWitness.mem_records_or_seedRandomised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SplitWitness.mem_records_or_seedRandomised

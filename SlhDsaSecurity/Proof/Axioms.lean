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

/-! Kernel dependency checks for the preparatory results. -/

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

/-! Framing closure, feasibility arithmetic, and the eligible-encoding count. -/

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

/-! All-queries-counted statements. -/

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


/-! Kernel dependency checks for the input-side coupling. -/

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

/-! Framing closure, feasibility arithmetic, and the eligible-encoding count. -/

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

/-! All-queries-counted statements. -/

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


/-! Kernel dependency checks for the FORS dispatch. -/

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

/-! Framing closure, feasibility arithmetic, and the eligible-encoding count. -/

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

/-! All-queries-counted statements. -/

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

/-! Kernel dependency checks for the blind comparison. -/

/-- info: 'SlhDsaSecurity.BlindComparison.flag_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.flag_one

/-- info: 'SlhDsaSecurity.BlindComparison.prob_touched_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.BlindComparison.prob_touched_eq

/-- info: 'SlhDsaSecurity.SeedDeferral.prob_run_meets_honest_key_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.SeedDeferral.prob_run_meets_honest_key_le

/-! The target, reduced to its two halves. -/

/-- info: 'SlhDsaSecurity.MainTheorem.totalSecurityBits_of_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.MainTheorem.totalSecurityBits_of_halves

/-! Kernel dependency checks for the game bridge. -/

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

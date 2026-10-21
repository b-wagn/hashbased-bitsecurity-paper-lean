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

/-- info: 'SlhDsaSecurity.HypertreeDispatch.cases_of_hypertreeFault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SlhDsaSecurity.HypertreeDispatch.cases_of_hypertreeFault

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

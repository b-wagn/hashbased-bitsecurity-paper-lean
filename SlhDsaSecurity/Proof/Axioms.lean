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

import SlhDsaSecurity.Proof.Parameters
import SlhDsaSecurity.Proof.Checksum
import SlhDsaSecurity.Proof.ForsCoverage
import SlhDsaSecurity.Proof.ForsMoments
import SlhDsaSecurity.Proof.Hashing

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

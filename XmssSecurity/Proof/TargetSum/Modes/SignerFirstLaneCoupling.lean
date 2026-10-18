import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.CountedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSampleBudget

/-! The statement's signer budget reaches the complete first-lane prefix coupling.
On its good branch, direct hazards and the actual source signer cost share that budget. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded DeterministicSigning CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Modes

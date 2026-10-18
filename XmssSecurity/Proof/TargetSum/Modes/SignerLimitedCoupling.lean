import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedFirstLaneExpected

/-! The unchanged signer-mode query bound controls both sides of the coupling to
the limited public first-lane experiment, including all post-collision executions. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded DeterministicSigning CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Modes

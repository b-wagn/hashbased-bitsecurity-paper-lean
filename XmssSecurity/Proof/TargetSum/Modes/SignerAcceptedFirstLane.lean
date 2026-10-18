import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedLoss

/-! The source encoding credit pays for the accepted first lane, including adversaries
that sometimes return fresh encodings. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct Deciding

end XmssSecurity.TargetSum.Modes

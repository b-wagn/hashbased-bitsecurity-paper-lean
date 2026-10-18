import XmssSecurity.Proof.TargetSum.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

/-- The five cryptographic failure mechanisms, without coordinate indices. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
deriving DecidableEq, Fintype

end XmssSecurity.TargetSum

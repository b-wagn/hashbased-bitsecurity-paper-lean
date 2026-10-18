import XmssSecurity.Proof.Generic.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

/-- The five cryptographic failure mechanisms, without coordinate indices. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
deriving DecidableEq, Fintype

end XmssSecurity.Generic

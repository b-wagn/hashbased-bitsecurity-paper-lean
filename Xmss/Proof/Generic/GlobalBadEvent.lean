import Xmss.Proof.Generic.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic

variable [Code]

/-- The five cryptographic failure mechanisms, without coordinate indices. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
deriving DecidableEq, Fintype

end Xmss.Generic

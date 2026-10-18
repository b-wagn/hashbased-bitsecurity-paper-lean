import XmssSecurity.Proof.Checksum.CappedSigningLogReplay

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum

/-- The five cryptographic failure mechanisms, without coordinate indices. -/
inductive GlobalBadEvent where
  | encoding
  | chain
  | suffixCollision
  | leaf
  | merkle
deriving DecidableEq, Fintype

end XmssSecurity.Checksum

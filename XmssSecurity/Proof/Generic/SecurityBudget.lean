import XmssSecurity.Proof.Generic.Code
import XmssSecurity.Proof.Generic.RandomOracle

namespace XmssSecurity.Generic

variable [Code]

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin Code.verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

end XmssSecurity.Generic

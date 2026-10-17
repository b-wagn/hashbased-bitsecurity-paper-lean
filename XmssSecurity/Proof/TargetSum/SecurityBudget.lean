import XmssSecurity.Proof.TargetSum.EncodingLemmas
import XmssSecurity.Proof.TargetSum.RandomOracle

namespace XmssSecurity.TargetSum

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

end XmssSecurity.TargetSum

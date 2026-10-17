import XmssSecurity.Proof.Checksum.EncodingLemmas
import XmssSecurity.Proof.Checksum.RandomOracle

namespace XmssSecurity.Checksum

/-- The elementary bad events used by the current classical reduction. -/
inductive BadEvent where
  | encoding
  | chain (chain : ChainIndex)
  | suffixCollision (step : Fin verificationChainHashes)
  | leaf
  | merkle (level : Fin treeHeight)
deriving DecidableEq, Fintype

end XmssSecurity.Checksum

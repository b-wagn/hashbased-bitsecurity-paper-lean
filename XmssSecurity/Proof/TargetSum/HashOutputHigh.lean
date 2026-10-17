import XmssSecurity.Proof.TargetSum.RandomOracle

namespace XmssSecurity.TargetSum

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity.TargetSum

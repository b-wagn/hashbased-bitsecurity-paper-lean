import XmssSecurity.Proof.Generic.RandomOracle

namespace XmssSecurity.Generic

variable [Code]

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity.Generic

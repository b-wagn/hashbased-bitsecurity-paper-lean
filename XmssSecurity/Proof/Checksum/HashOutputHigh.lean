import XmssSecurity.Proof.Checksum.RandomOracle

namespace XmssSecurity.Checksum

def hashOutputHigh (output : HashOutput) : Digest :=
  (Rom.hashOutputEquivDigestPair output).1

end XmssSecurity.Checksum

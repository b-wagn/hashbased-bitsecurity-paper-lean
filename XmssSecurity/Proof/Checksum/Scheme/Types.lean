import XmssSecurity.Statement.Scheme.Checksum

/-!
# Keys and signatures of the Checksum instance

The secret keys and signatures of the generic construction for the `numChains` chains of this
encoding.
-/

namespace XmssSecurity.Checksum

abbrev SecretKey := XmssSecurity.SecretKey numChains
abbrev Signature := XmssSecurity.Signature numChains

end XmssSecurity.Checksum

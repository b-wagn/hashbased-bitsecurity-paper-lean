import XmssSecurity.Statement.Scheme.TargetSum

/-!
# Keys and signatures of the TargetSum instance

The secret keys and signatures of the generic construction for the `numChains` chains of this
encoding.
-/

namespace XmssSecurity.TargetSum

abbrev SecretKey := XmssSecurity.SecretKey numChains
abbrev Signature := XmssSecurity.Signature numChains

end XmssSecurity.TargetSum

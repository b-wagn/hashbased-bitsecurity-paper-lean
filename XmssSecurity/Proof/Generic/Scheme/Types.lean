import XmssSecurity.Proof.Generic.Code

/-!
# Keys and signatures for the code

The secret keys and signatures of the generic construction for the `numChains` chains of this
encoding.
-/

namespace XmssSecurity.Generic

variable [Code]

abbrev SecretKey := XmssSecurity.SecretKey Code.numChains
abbrev Signature := XmssSecurity.Signature Code.numChains

end XmssSecurity.Generic

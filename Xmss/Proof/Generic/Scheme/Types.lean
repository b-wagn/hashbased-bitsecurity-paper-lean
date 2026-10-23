import Xmss.Proof.Generic.Code

/-!
# Keys and signatures for the code

The secret keys and signatures of the generic construction for the `numChains` chains of this
encoding.
-/

namespace Xmss.Generic

variable [Code]

abbrev SecretKey := Xmss.SecretKey Code.numChains
abbrev Signature := Xmss.Signature Code.numChains

/-! ## The subjects of the construction

`Hashing.lean` and `Construction.lean` fill these; they are declared here so that each of those
files can `open` the subjects it builds on. -/

namespace Hashing end Hashing
namespace Wots end Wots
namespace Merkle end Merkle
namespace Verify end Verify
namespace Keygen end Keygen
namespace Signing end Signing
namespace Util end Util

end Xmss.Generic

import Xmss.Proof.Generic.IdealStatement

namespace Xmss.Generic

variable [Code]

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end Xmss.Generic

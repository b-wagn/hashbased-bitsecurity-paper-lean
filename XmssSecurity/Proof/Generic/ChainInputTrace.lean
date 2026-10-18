import XmssSecurity.Proof.Generic.IdealStatement

namespace XmssSecurity.Generic

variable [Code]

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end XmssSecurity.Generic

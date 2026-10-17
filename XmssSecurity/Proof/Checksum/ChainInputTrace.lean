import XmssSecurity.Proof.Checksum.IdealStatement

namespace XmssSecurity.Checksum

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end XmssSecurity.Checksum

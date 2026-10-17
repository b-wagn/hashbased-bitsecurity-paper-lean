import XmssSecurity.Proof.TargetSum.IdealStatement

namespace XmssSecurity.TargetSum

inductive AttackerAction where
  | hash (input : HashInput)
  | sign (request : SignRequest) (signature : Option Signature)
deriving DecidableEq

abbrev AttackerActionTrace := List AttackerAction

end XmssSecurity.TargetSum

import Xmss.Proof.Generic.CappedExecution.SourceDirectTrace

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic.CappedExecution

variable [Code]

def directHashActionCost :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inr _) => 1
  | _ => 0

@[simp]
theorem attackerActionFragment_hashInputs_length
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs.length =
      directHashActionCost input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput <;> rfl
  · rfl

end Xmss.Generic.CappedExecution

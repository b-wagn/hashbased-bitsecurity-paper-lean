import XmssSecurity.Proof.Generic.CappedChain.EncodingQueryBound
import XmssSecurity.Proof.Generic.ChainInputTrace
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec

namespace XmssSecurity.Generic.CappedChain

variable [Code]

abbrev AttackerAction := XmssSecurity.Generic.AttackerAction

abbrev AttackerActionTrace := XmssSecurity.Generic.AttackerActionTrace

def AttackerAction.hashInput? : AttackerAction → Option HashInput
  | .hash input => some input
  | .sign _request _signature => none

def AttackerAction.signingEntry? :
    AttackerAction → Option ((_request : SignRequest) × Option Signature)
  | .hash _ => none
  | .sign request signature => some ⟨request, signature⟩

def AttackerActionTrace.hashInputs (trace : AttackerActionTrace) : List HashInput :=
  trace.filterMap AttackerAction.hashInput?

@[simp]
theorem AttackerActionTrace.hashInputs_append
    (left right : AttackerActionTrace) :
    (left ++ right).hashInputs = left.hashInputs ++ right.hashInputs := by
  simp [AttackerActionTrace.hashInputs]

/-- The number of encoding-hash inputs in an attacker trace. -/
noncomputable def AttackerActionTrace.encodingInputCount
    (parameter : PublicParameter) (trace : AttackerActionTrace) : Nat :=
  trace.hashInputs.countP (fun input => (encodingInputLeafIndex? parameter input).isSome)

theorem AttackerActionTrace.encodingInputCount_append (parameter : PublicParameter)
    (left right : AttackerActionTrace) :
    (left ++ right).encodingInputCount parameter =
      left.encodingInputCount parameter + right.encodingInputCount parameter := by
  simp only [AttackerActionTrace.encodingInputCount, AttackerActionTrace.hashInputs_append,
    List.countP_append]

def AttackerActionTrace.toSigningLog
    (trace : AttackerActionTrace) : QueryLog SigningSpec :=
  trace.filterMap AttackerAction.signingEntry?

@[simp]
theorem AttackerActionTrace.toSigningLog_append
    (left right : AttackerActionTrace) :
    (left ++ right).toSigningLog = left.toSigningLog ++ right.toSigningLog := by
  simp [AttackerActionTrace.toSigningLog]

def attackerActionFragment
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) : AttackerActionTrace :=
  match input with
  | .inl (.inl _) => []
  | .inl (.inr hashInput) => [.hash hashInput]
  | .inr request => [.sign request output]

@[simp]
theorem attackerActionFragment_uniform
    (index : unifSpec.Domain) (output : unifSpec.Range index) :
    attackerActionFragment (.inl (.inl index)) output = [] := rfl

@[simp]
theorem attackerActionFragment_hash (input : HashInput) (output : Digest) :
    attackerActionFragment (.inl (.inr input)) output = [.hash input] := rfl

@[simp]
theorem attackerActionFragment_sign
    (request : SignRequest) (signature : Option Signature) :
    attackerActionFragment (.inr request) signature = [.sign request signature] := rfl

@[simp]
theorem attackerActionFragment_hashInputs
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs =
      match input with
      | .inl (.inr hashInput) => [hashInput]
      | _ => [] := by
  cases input with
  | inl worldInput => cases worldInput <;> rfl
  | inr request => rfl

@[simp]
theorem attackerActionFragment_toSigningLog
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).toSigningLog = signingLogFragment input output := by
  cases input with
  | inl worldInput => cases worldInput <;> rfl
  | inr request => rfl

end XmssSecurity.Generic.CappedChain

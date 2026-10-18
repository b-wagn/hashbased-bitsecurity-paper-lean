import XmssSecurity.Proof.Checksum.CappedEncodingQueryBound
import XmssSecurity.Proof.Common.EncodingQueryAccounting

open OracleComp OracleSpec

namespace XmssSecurity.Checksum.CappedChain

noncomputable def unloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp) := by
  classical
  intro input
  cases input with
  | inl worldInput =>
      exact romImpl worldInput
  | inr request =>
      exact simulateQ romImpl
        (Concrete.scheme.sign secretKey request.epoch request.message)

theorem unloggedMappedAdversaryImpl_apply_inl
    (publicKey : PublicKey) (secretKey : SecretKey)
    (worldInput : OracleWorld.Domain) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inl worldInput) =
      romImpl worldInput := by
  rfl

theorem unloggedMappedAdversaryImpl_apply_inr
    (publicKey : PublicKey) (secretKey : SecretKey)
    (request : SignRequest) :
    unloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      (simulateQ romImpl
        (Concrete.scheme.sign secretKey request.epoch request.message) :
          StateT (QueryCache HashSpec) ProbComp (Option Signature)) := by
  rfl

end XmssSecurity.Checksum.CappedChain

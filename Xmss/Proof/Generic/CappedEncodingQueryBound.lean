import Xmss.Proof.Generic.CappedSigningCacheTrace

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

noncomputable def cappedSourceUnloggedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request =>
      exact precomputedScheme.sign secretKey request.epoch request.message

theorem cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq
    (publicKey : PublicKey) (secretKey : SecretKey) :
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey).withTraceAppend
        signingLogFragment =
      (forwardOracles + signingOracle precomputedScheme secretKey) := by
  funext input
  cases input with
  | inl worldInput =>
      apply WriterT.ext
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment, forwardOracles]
      rfl
  | inr request =>
      simp [cappedSourceUnloggedMappedAdversaryImpl, signingLogFragment, signingOracle]

end Xmss.Generic

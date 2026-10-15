import XmssSecurity.Statement.Security.SUFCMA

/-!
# Standard unforgeability under chosen-message attacks

This is the non-strong version of the synchronized unforgeability experiment.
A forgery must verify for an epoch/message pair never submitted to the signing
oracle. A request counts as submitted even if the signer returns `none`.
Changing only the signature on a previously requested pair does not win.

The scheme, adversaries, random-oracle model, one-request-per-epoch transcript
condition, and sixteen counting modes are shared with SUF-CMA. Verification is
performed before the freshness check, so accounting is independent of which
freshness condition is used.
-/

open OracleComp OracleSpec

namespace XmssSecurity.EUFCMA

open SUFCMA

namespace SigningTranscript

/-- The forgery's epoch/message pair was submitted, regardless of the answer. -/
def ContainsRequest {Msg Sig : Type} {L : ℕ}
    (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request

instance {Msg Sig : Type} {L : ℕ} [DecidableEq Msg]
    (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L) :
    Decidable (ContainsRequest log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1 = forgery.request))

end SigningTranscript

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The standard unforgeability game, without query accounting. -/
def game [DecidableEq Msg]
    (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) : OracleComp spec Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery Msg Sig L × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      (QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) +
        signingOracle scheme sk)
      (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SUFCMA.SigningTranscript.Valid log ∧ ¬SigningTranscript.ContainsRequest log forgery) && verified

/-- Standard unforgeability with the same charged work as the strong experiment. -/
def gameCounted [DecidableEq Msg] (mode : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) : OracleComp spec (Bool × ℕ) := do
  let ((pk, sk), keygenCharged) ← charge (costIf mode.keygen cost) scheme.keygen
  let (((forgery, adversaryCharged), log) :
      (Forgery Msg Sig L × Multiplicative ℕ) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
        signingOracleCounted (costIf mode.signer cost) (if mode.requests then 1 else 0) scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCharged) ← charge (costIf mode.verifier cost)
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (SUFCMA.SigningTranscript.Valid log ∧ ¬SigningTranscript.ContainsRequest log forgery) && verified,
    keygenCharged + Multiplicative.toAdd adversaryCharged + verifierCharged)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- EUF-CMA in the random-oracle model, with fresh epoch/message pairs. -/
noncomputable def notion [DecidableEq Msg] (mode : CountingMode) :
    SecurityNotion
      (SynchronizedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) where
  Adversary := SUFCMA.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (gameCounted mode (RandomOracleModel.hashCost Input Output) scheme adversary)

end XmssSecurity.EUFCMA

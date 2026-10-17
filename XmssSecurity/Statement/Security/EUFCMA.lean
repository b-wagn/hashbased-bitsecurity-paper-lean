import XmssSecurity.Statement.Security.SUFCMA

/-!
# Standard unforgeability under chosen-message attacks

The experiment `EUFCMA_SIG(A)` of the definition of unforgeability of the manuscript: the experiment
`SUFCMA_SIG(A)` of `SUFCMA.lean`, with the same oracles and the same query counts, except that a
forgery must be for an epoch/message pair `(ep*, m*)` that is not in the table `Signed`, i.e. for
which `(m*, σ) ≠ Signed[ep*]` for every `σ ∈ Σ ∪ {⊥}`. A request counts as submitted even if the
signer returned `⊥`. Changing only the signature on a previously requested pair does not win.
-/

open OracleComp OracleSpec

namespace XmssSecurity.EUFCMA

open SUFCMA

namespace SigningTranscript

/-- The forgery's epoch/message pair is in the table `Signed`, regardless of the answer. -/
def ContainsRequest {Msg Sig : Type} {L : ℕ}
    (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request

instance {Msg Sig : Type} {L : ℕ} [DecidableEq Msg]
    (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L) :
    Decidable (ContainsRequest log forgery) :=
  inferInstanceAs (Decidable (∃ entry ∈ log, entry.1 = forgery.request))

end SigningTranscript

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The experiment `EUFCMA_SIG(A)`: as `SUFCMA.experiment`, with the winning condition requiring
an epoch/message pair never submitted to the signing oracle. -/
def experiment [DecidableEq Msg] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × QueryCounts) := do
  let ((pk, sk), keygenCounts) ←
    countQueries (fun t => QueryCounts.single .keygen (cost t)) scheme.keygen
  let (((forgery, adversaryCounts), signed) :
      (Forgery Msg Sig L × Multiplicative QueryCounts) × QueryLog (SigningSpec Msg Sig L)) ←
    ((simulateQ
      ((QueryImpl.ofLift spec
          (StateT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => QueryCounts.single .hash (cost t)) +
        countedSigningOracle cost scheme sk)
      (adversary.main pk)).run.run [])
  let (verified, verifierCounts) ← countQueries (fun t => QueryCounts.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (¬SigningTranscript.ContainsRequest signed forgery) && verified,
    keygenCounts + Multiplicative.toAdd adversaryCounts + verifierCounts)

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- EUF-CMA in the random-oracle model, counting as `SUFCMA.securityGame`. -/
noncomputable def securityGame [DecidableEq Msg] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind where
  Adversary := SUFCMA.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L
  experiment := fun scheme adversary =>
    RandomOracleModel.run
      (EUFCMA.experiment (RandomOracleModel.hashCost Input Output) scheme adversary)

end XmssSecurity.EUFCMA

import XmssSecurity.Statement.Security.SUFCMA

/-!
# Standard unforgeability under chosen-message attacks

The experiment `EUFCMA_SIG(A)` of the definition of unforgeability of the manuscript: the
experiment of `SUFCMA.lean`, with the same oracles and the same query counts, except that a
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

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output]

/-- EUF-CMA in the random-oracle model: the experiment of `SUFCMA.lean`, in which a forgery is
fresh if its epoch/message pair is not in the table `Signed`. -/
noncomputable abbrev securityGame [DecidableEq Msg] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  SUFCMA.gameWith fun signed forgery => ¬SigningTranscript.ContainsRequest signed forgery

end XmssSecurity.EUFCMA

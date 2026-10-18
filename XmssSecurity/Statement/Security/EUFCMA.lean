import XmssSecurity.Statement.Security.SUFCMA

/-!
# Standard unforgeability under chosen-message attacks

The SUF-CMA experiment with a stronger freshness condition: the forgery's epoch/message pair
must be absent from `Signed`, regardless of whether the recorded signing attempt succeeded.
As in SUF-CMA, only the first request at each epoch is recorded.
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

/-- EUF-CMA: the forgery's epoch/message pair must be absent from `Signed`. -/
noncomputable abbrev securityGame [DecidableEq Msg] :
    SecurityGame (EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
      QueryKind :=
  SUFCMA.gameWith fun signed forgery => ¬SigningTranscript.ContainsRequest signed forgery

end XmssSecurity.EUFCMA

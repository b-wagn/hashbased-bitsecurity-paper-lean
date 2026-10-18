import XmssSecurity.Proof.Generic.CappedEncodingEventProbability
import XmssSecurity.Proof.Generic.CappedUnifiedStructuralCollision

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)

/-- A winning encoding collision, together with a signing whose randomizer was already cached
(a prehit) and whose signed digest another cached encoding input of its epoch shares. -/
def WinningEncodingPrehitOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
    ∃ entry ∈ execution.2.1.2, entry.EncodingInputPrehit execution.1.secretKey ∧
      entry.PrehitPartnered execution.1.secretKey execution.2.1.1

theorem WinningEncodingPrehitOccurs.hasEncodingInputPrehit
    {execution : CappedEncodingTraceExecution} (h : WinningEncodingPrehitOccurs execution) :
    WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      execution.2.1.2.HasEncodingInputPrehit execution.1.secretKey := by
  obtain ⟨hencoding, entry, hentry, hprehit, _⟩ := h
  exact ⟨hencoding, entry, hentry, hprehit⟩

end XmssSecurity.Generic

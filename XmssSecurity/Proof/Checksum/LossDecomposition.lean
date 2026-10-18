import XmssSecurity.Proof.Checksum.UnifiedBadEvent

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum

abbrev CappedEncodingTraceExecution :=
  GameOutcome × ((QueryCache HashSpec × SigningCacheTrace) × EncodingActionTrace)

def WinningEncodingPrehitOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
    execution.2.1.2.HasEncodingInputPrehit execution.1.secretKey

end XmssSecurity.Checksum

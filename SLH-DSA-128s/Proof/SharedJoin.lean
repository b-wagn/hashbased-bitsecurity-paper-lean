import «SLH-DSA-128s».Proof.Target
import «SLH-DSA-128s».Proof.SigningFaithful
import «SLH-DSA-128s».Proof.RandomiserRecord
import «SLH-DSA-128s».Proof.ClassGrowth
import «SLH-DSA-128s».Proof.AnswerSide
import «SLH-DSA-128s».Proof.RedrawCell
import «SLH-DSA-128s».Proof.RecordedBudget
import «SLH-DSA-128s».Proof.WarmedGame

/-!
# The shared side's events, on a paired run

The shared side's events (such as `RoutedSplit.InputBad`) are stated on a paired run: the walk
and the game side by side. **They are stated on `RecordedPair`, the pair with the run's own record
retained**, because some of them read the record and the record is not a function of the trace
(the cache keeps neither multiplicity nor caller). `traceOf` and `recordedTraceOf` read the trace
off a pair, and `recordOf` reads the record. -/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharedJoin

open Security WarmedGame RoutedSplit ReplayGate Target RandomiserProvenance RandomiserRecord


/-- The value of a paired run (the walk's cells and the game), before its record is retained. -/
abbrev Pair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    ((Outcome × Nat) × QueryCache HashSpec)

/-- The same, with the run's own record retained. -/
abbrev RecordedPair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)

/-- The trace the shared side's events read, assembled from a paired run's value. -/
abbrev traceOf (pair : Pair) : RoutedSplit.Trace := ((pair.1.1, pair.2.1), pair.2.2)

/-- The same, read off a recorded pair by forgetting its record. -/
abbrev recordedTraceOf (pair : RecordedPair) : RoutedSplit.Trace :=
  traceOf (forgetRecord pair)

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  RecordedTail.recordedAfterSeeds RecordedTail.recordedTail

/-- The run's own record. -/
abbrev recordOf (pair : RecordedPair) : Multiset Bytes := pair.2.1.1.2

end SlhDsaSecurity.SharedJoin

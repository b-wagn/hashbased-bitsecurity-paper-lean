import SlhDsaSecurity.Proof.AnswerJoin
import SlhDsaSecurity.Proof.LateProvenance
import SlhDsaSecurity.Proof.ProbeContainment

/-!
# The target, from the obligations that are left

`Obligations.target_of_charges_fused` closes the target from two obligations at a refining tail.
This file supplies the tail — the fused presentation — and composes the two, which is the only
statement that tests whether the pieces fit.

**It is a seam check, and it is written as one.** Each hypothesis is the obligation its owner
has to meet, in the spelling the consumer uses, and the composition is a single application with
nothing in between: no rewriting, no `convert`, no adapter. If a producer's shape and a
consumer's drift apart, this stops elaborating, and it stops at the seam rather than three files
later. The places where one file's output feeds its own next lemma are not covered here, and do
not need to be — the mismatches have all been between owners.

**The refining tail is the recorder's**, and the one equation it owes the target is that its
results forget to the game's. That is `forgetFused_map`, and it holds as an equality of
computations: the recorder answers every query exactly as the shared oracle does and writes its
recordings beside the answer, so dropping them returns the game.

What the statement says, read as a list, is what the proof rests on: the answer half's
obligation with late disclosure ruled out, and the shared half's with it paid. The second is
discharged in `ObligationShapes`; the first is the answer side's, and is the one whose
restatement is outstanding.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FinalAssembly

open Security CanonicalGraph WarmedGame RoutedSplit Target AnswerSide

/-- What a fused result forgets to: the game's own outcome, count and cache. -/
def forgetFused (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    (Outcome × Nat) × QueryCache HashSpec :=
  ((result.1.1.1, result.1.2), result.2.1)

/-! ## The same, at what the answer half proves

The obligation above states the answer half's bound with a `2 ^ -126` beside the `2 ^ -141`, and
the half adds it by a weakening: `AnswerSide.prob_answerBad_good_le_of_caps_recorded_narrow`
concludes `q / 2 ^ 128 + 1 / 2 ^ 141` and `AnswerJoin` reaches the stated right-hand side by
`le_add_right`. Read at what is proved, the ledger's defect budget falls from six units of
`2 ^ -128` to two and the margin against key generation's reservation rises from `247` to `251`.

Both readings are here because the `2 ^ -126` is still spent on one route — the producer that
takes the seed leftover as a probability hypothesis rather than as a conjunct. The narrow
producers that do not spend it are proved; this is the shape they land in. -/

end SlhDsaSecurity.FinalAssembly

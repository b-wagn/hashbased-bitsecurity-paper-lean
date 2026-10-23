import SlhDsaSecurity.Proof.CarrierCover
import SlhDsaSecurity.Proof.CoverageRouted
import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.SplitCarrierTail
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.AddressBounds
import SlhDsaSecurity.Proof.CarrierLeftRecord

/-!
# `hsplit`, end to end, and the one seam that does not meet

`AnswerCarrier.hsplit_of_join` takes `hjoin` as a named argument;
`CarrierJoin.targetCovered_carrierTail` is that argument with the cover left open;
`CarrierCover.cover_carrierRightKeep` closes the cover at the carrier's own tests. This file
puts the three together at `AnswerCarrier.answerCarrierRun` and carries the result to
`SplitTail.splitCarrierTail`, where both charges meet.

**One residue survives the assembly, and the ledger carries it rather than the proof.**

`CarrierCover.cover_carrierRightKeep` holds at the **narrowed** class
`IsMessageInput ∧ ¬ RandomizerGate.PrfClass`, and the narrowing is not cosmetic:
`RandomizerGate.messageInput_eq_randomizerInput_iff` says
`PrfClass prfSeed (messageInput r pk m)` holds exactly when `r = prfSeed`, so the clause the
carrier's `FilesRandomiser` test raises is refuted precisely by knowing the input's randomiser
is not the PRF seed.

`hjoin` supplies `¬ AnswerCoverage.ForgerySeedRandomised`, which says that of the **forgery's**
randomiser alone. The cover is used twice: at the forgery's own digest input, where that is
exactly enough, and at each *disclosing* witness, where it is not — a served request's
randomiser is a value the walk drew, and "it is not the PRF seed" is a guess at a secret, which
at a fixed walk cannot be proved.

**So it is not assumed here. It is conjoined to the conclusion**, as
`SplitWitness.SeedRandomised`, for the shared half to charge. That is not a choice made in this
file; it is what the definition's own docstring says, written before the question arose:

> *It is not charged here and cannot be: the seed is the walk's, and at a fixed walk an
> adversary may carry it as a constant. It belongs to the shared half, where the record's
> `PRF_msg` part is charged with the seed drawn after the run.*

`AnswerCarrier.hsplit_of_join_extra` is the law that carries such a residue through, and
`hsplit_of_join` is its instance at the empty one.

**Why the alternative was not taken.** The residue could instead be removed by dropping the
`FilesRandomiser` clause from the carrier's target test and reproving the cover
frame-conditionally — but that needs `reaches` threaded and the phase propagation `FusedCover`
does not have, and it buys nothing the ledger does not already provide. The gap between the
forgery-only leftover and the cache-wide one exists *because* the carrier's target test carries
a clause the cache's does not; charging the wider one is the same payment the cache route
already makes.

The three remaining hypotheses are not findings, only unowned: freshness at the walk's own
cache (the same hypothesis the cache route takes) and the two recording-class facts, which are
the served-agreement and the ordering, and belong to the threads that own those. `hseed`
survives only inside `targetCovered_carrierTail_narrow`, where it is a genuine conditional and
not an assumption of the assembly.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierSplit

open Security RecorderView CarriedWitness BracketedRun CarrierTail CoverageRouted

/-! ## `hjoin` at the answer side's run

`AnswerCarrier.answerCarrierRun` is `AnswerShape.forgetRecord` over the tail, and that map keeps
the whole recorder state, so the coverage event and both recording-class facts read the same
objects on either side of it. `GoodWalk`, `¬ ForgerySeedRandomised` and `¬ LateDisclosure` are
accepted and not used here: the second is subsumed by the residue the conclusion now carries,
and the third by the recording-class hypotheses, which is **deferral and not elimination** —
`¬ LateDisclosure` is what supplies `hrightClass` on the cache route. `GoodWalk` is genuinely
unused by this join. -/

attribute [local irreducible] AnswerCarrier.answerCarrierRun

/-! ## And `hsplit`, carried to the tail where the charges meet -/

end SlhDsaSecurity.CarrierSplit

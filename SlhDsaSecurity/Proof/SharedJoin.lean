import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.AnswerSide
import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.RecordedBudget
import SlhDsaSecurity.Proof.WarmedGame

/-!
# The shared side's charges, added

`Obligations.SharedCharged` is one bound on `InputBad ∨ RandomiserBad`, and several charges pay
for it. This file is the join: each taken in the shape its owner produces, added, and discharged
against `(q - 2 ^ subtreeHeight + 259) / 2 ^ 128`.

**It is stated at `RandomiserRecord.recordedPairedRun`, the walk and the game with the record
retained**, and that is forced rather than convenient. Three of the charges read only the trace;
the randomiser's does not — `RecordMeetsPrfClass` reads the record, and the record is not a
function of the trace, since the cache keeps neither multiplicity nor caller. The only
trace-level version is an existential over records, which this file's own reasoning rules out as
near-vacuous. Nothing is paid for the change: `RandomiserRecord.pairedRun_eq_map` is an equality
of computations, so `probEvent_pairedRun_eq` moves every trace-level event across exactly, and
`InputBad`, `RandomiserBad` and the ordering defect's event all factor through `forgetRecord`
unchanged.

**What the charges are, at the split that exists.** A deferral reads its count off the run
*before* the secret is drawn, so the randomiser defect's count has to be **prf-free** and the
three-way classification of the record by first block is not available to it — two of those
parts name `SK.prf`. What is available is `canonical ⊎ offCanonical`: the record's entries that
are canonical inputs of the walk's own cells, and the rest, which names only the walk. So:

* the input half pays the canonical part, plus the forgery's own 259 claims;
* the randomiser defect pays the off-canonical part;
* the ordering defect pays its own count, which under this split is **not** a share of the
  record — the three-way split that made it one is gone;
* the signer's coincidence pays twice the served requests.

The first two partition the record and the last is disjoint from both. The ordering defect's is
the term that no longer has a home in the partition, and the sum below takes it as a fourth
count without claiming otherwise.

**The counts have to be expectations, and that is the one thing the join forces.** Each charge
would naturally be stated at a *cap* — a constant `L` with the count at most `L` on every
supported run. Caps cannot be added: the partition holds **per run**, and the split between
`work` and `served` is a property of the run, so an almost-sure cap for each count has to cover
its own worst run and four worst-case caps are four budgets. Expectations add where caps do not,
because they add pathwise (`ClassExpectation.expected_add`, `expected_le_of_le`). That is the
move the answer side already made for its coverage term, and
`ClassExpectation.add_le_of_shared_budget` is its two-term form.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharedJoin

open Security WarmedGame RoutedSplit ReplayGate Target RandomiserProvenance RandomiserRecord


/-- What the shared side's events were stated on before the record had to be kept. -/
abbrev Pair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    ((Outcome × Nat) × QueryCache HashSpec)

/-- What they are stated on now: the same, with the run's own record retained. -/
abbrev RecordedPair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)

/-- The trace the shared side's events read, assembled from a paired run's value. -/
abbrev traceOf (pair : Pair) : RoutedSplit.Trace := ((pair.1.1, pair.2.1), pair.2.2)

/-- The same, read off a recorded pair by forgetting its record. -/
abbrev recordedTraceOf (pair : RecordedPair) : RoutedSplit.Trace :=
  traceOf (forgetRecord pair)

/-! ## The counts, read off the record

Each charge's count is a **part of the run's own record**, and the parts are named here so that
the owners prove containments into one observable rather than three different counts.

Why the record and not the cache's growth: a sensitive probe may be answered from the walk's
table and install nothing, so growth cannot report it; and the plain pair carries no split
counter, so a slot-based count has nowhere to live. The record has neither problem, and it is
the observable the accounting is already written in — `Multiset.card record = counts.work`
exactly, which is what ties every part of it to the budget.

**What each owner proves is a containment, not a conversion.** A charge keeps whatever probe
list its own handler produces and shows that list sits inside the record's part of its class;
`ProbesIn` is that obligation and `card_le_of_probesIn` is what it buys. Nothing has to be
restated at a counter.

The two parts are disjoint **by construction, on every run**: `recordMessageClass` carries
`¬ AimsSomewhere` as a conjunct of its own filter, so an input in both parts would have to aim
and not aim. `card_parts_le_record` takes no hypotheses at all, and neither does the arithmetic
that follows it — the shared side's accounting is not conditioned on the walk.

What the good walk *is* for is one step further in, and it is a different statement.
`mem_recordMessageClass` has to put a message input of the record **into** the message-class
part, which needs that input not to aim; that is `not_aimsSomewhere_messageInput`, where a
canonical input opens with `PK.seed ‖ ADRS` and a message input with a randomiser and
`HashSeparation` separates them once the key is no coincidence.

So the two cardinalities add to at most the record's, which is the work, which with key
generation's reserved spend is `q - 2 ^ subtreeHeight`. That is `card_parts_le_budget`, and with
the forgery's `259` claims against the `512` key generation puts back it is the whole of the
shared side's arithmetic. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  RecordedTail.recordedAfterSeeds RecordedTail.recordedTail

/-- The run's own record. -/
abbrev recordOf (pair : RecordedPair) : Multiset Bytes := pair.2.1.1.2

/-! ## From a part of the record to the budget -/

/-! ## The record itself against the budget

`card_parts_le_budget` bounds the two parts, and a consumer that needs the **record** cannot get
there from it: `card_parts_le_record` points the other way, so the two compose to nothing. What
does give it is what is already inside that proof — the record's cardinality *is* the work
count, and the work count plus the subtree leaves fit in the budget. Stated on its own because
two live routes need it and neither needs the parts.

**It is the same shape as `card_parts_le_budget` with the first step dropped.** That is worth
saying rather than hiding: a lemma whose proof contains a more general statement than its own
conclusion is a lemma that will be re-derived, and the fix is to state the general one beside
it, not to rewrite the specific one. -/

/-! ## The adapters, so the bridge is applied rather than merely present

`ProbesIn` and `card_le_of_probesIn` say what an owner has to prove and what it buys, but
getting from there to the hypotheses the join actually takes is four more lines, and two of the
three owners would each discover them. So the join does it.

The adapters also take the charge **per walk**, which is both the habit and the shape the
charges naturally prove: a charge is proved at a fixed walk, where the cells are fixed, and the
averaging is a separate step. Asking the owner for the paired form would be asking them to
perform that step; the adapter performs it instead.

A bridge that exists but sits unapplied is indistinguishable from a missing one at the moment
someone hands work over, and the cost lands on whoever assembles. -/

/-! ## The two per-walk adapters, neither of which has a consumer

Both are sound and neither can serve the owner it was written for. `hinput_of_probesIn` takes
its charge per walk, which the input half cannot give, for the reason its own docstring sets
out. `hordering_of_probesIn` takes an `ordering` that is a predicate of the recorded pair, and
the ordering defect is not one — a recorded pair carries no recordings, and which side an entry
was filed on is the whole content of the defect. `SharedAssembly` closes the obligation without
either. They are kept until it closes, and the hazard a reader meeting them first should be
spared is reaching for one on the strength of its name. -/

/-! ## The join, at the three terms the repair leaves

The input half at the record's canonical part, the forgery's `259` claims, and the ordering
defect at the record's message-class part. The randomiser defect's term and the signer's
coincidence are gone with the proxy they paid for.

The shared event is taken **abstractly**. Which disjuncts the split names is the split's
business and is still moving — the third stops being `ReplayGate.RandomiserBad` and becomes a
late-disclosure event, which may arrive as a hypothesis on the answer side rather than as a
disjunct — and the sum does not care: all it needs is that the event is covered by the input
half's and the ordering defect's, which is `hcover`.

`hshare` is gone too. The two counts are parts of one record and disjoint by construction, so
`card_parts_le_budget` proves what used to be assumed. That is the whole of the shared side's
arithmetic, and it closes on the nose: `card canonical + card message-class ≤ work`, and
`work + 2 ^ subtreeHeight ≤ q`, so the three terms are `(q - 2 ^ subtreeHeight) + 259`. -/

/-! ## The cover costs nothing

`hcover` reads like the step where the split is justified, and at the instantiation the shared
side actually uses it is **excluded middle** and nothing else. Taking `inputBad` to be the
shared event itself, the two parts are "the event with the defect ruled out" and "the defect",
and those cover the event for *any* `ordering` whatever.

Two things follow, and both are worth saying where the hypothesis used to sit.

* It is free, so `sharedCharged_of_two` below carries it internally instead of owing it. The
  shared side's two obligations are the two charges; there is no third.
* It does not look at `ordering`, so **the ordering thread may restate its event however it
  likes** — on the record alone, on the recordings, on the final cache — and this step does not
  move. The thread that found `hordering_of_probesIn` cannot accept an event defined by which
  side an entry was filed on, because a `RecordedPair` carries no recordings; whatever it
  settles on, the cover is the same two lines. The content of the split lives entirely in
  `hinput`, which is where `¬ ordering` is *assumed* and has to be converted into a charge
  against the aiming part. -/

/-! ## The four-term union-bound route, superseded

Everything from here to the end of the file is the route built when the split still named a
randomiser defect and the signer's seed coincidence: four events, four counts, one budget.
The two-way split retired the first and the replay branch's closure retired the second, and
`SharedAssembly.sharedCharged_of_parts` now closes `Obligations.SharedCharged` from the input
half's bullet and the ordering term alone. Nothing outside this file reaches any of it.

It is retained until the obligation closes, not because anything here is wrong — it is not —
but because deleting a route while two owners are still landing is the trade that has cost
twice. `SignerEvent` goes with it when it goes.

The shared event is covered by the four, and this is the only step that knows which event is
which. Everything after it is arithmetic on the counts.

The randomiser defect's half of it is no longer a hypothesis: `RandomiserRecord.randomiserBad_dichotomy`
proves it at this presentation, with the record a value of the run rather than a witness. -/

/-! ## The join, at expectations

The four counts are read off the recorded paired run, and the only thing asked of them is that
they stay inside the budget **on every supported run**. `ClassExpectation.expected_add` then
makes the four expectations add to the expectation of the sum, and `expected_le_of_le` bounds
that by the budget. No charge is bounded on its own. -/

/-! ## The join, at constants

The same thing with the four counts constant. It is kept because a cap-shaped charge produces
exactly this, and it is sound — but its four constants must be bounds on the *expected* counts,
not on the counts themselves, for the reason in the header. -/

/-! ## The obligation

What each owner has to deliver, with the randomiser defect's reduction already proved and the
signer's condition already fixed. Only the four bounds and the budget's pathwise inequality are
left. -/

/-! ## The signer's coincidence, in expectation form

`ClassGrowth.run_splitCost_eq_map` identifies the split-counted run with the plain one, so the
charge may be read at the instrumented presentation and the bound carried back. Done that way
the signer's coincidence comes out in expectation form with no new machinery, which is what the
answer side's coverage term did.

**It lands at the wrong count, and the reason is a fact about what the counter can see.**
`ClassGrowth.splitCost` is indexed by the **input**: one unit of the inside slot for a hash call
at an in-class input, whoever makes it. The adversary's in-class call and the signer's are calls
at the *same* input — that is the search attack restated — so no input-indexed cost can charge
one and not the other, and what comes out is the expectation of **every** in-class hash call.

A counter wrapped around the signer's own sub-computation does not repair it either, and the
same attack says why: with `SK.prf` hardcoded the adversary queries `N` framings of its own,
keeps the one whose answer hits, and makes **one** request. The signer then makes two in-class
calls and `served` is one, while the event fires at about `N / 2 ^ 128`. So no bound shaped
`Pr[event] ≤ f(the signer's own in-class calls)` holds for any `f`.

What makes `2 · served` correct is the **branch**, not a counter: on runs where the record does
not meet the class, the in-class entries are the signer's own and
`RandomiserProvenance.growthAtMostOn_prfClass_of_clean` gives `2 · served` with no instrumentation
at all. `SignerEvent` is that conditioned event, and the charge for it is what the join still
waits on. Neither generic charge reaches it: `ClassExpectation.prob_bad_le_expected_cost` and
`PotentialCharge.prob_fired_le` both run at the shared oracle, and the condition is about *who*
made a call, which that oracle cannot see — correctly, since the two callers' in-class calls are
calls at the same input. -/

end SlhDsaSecurity.SharedJoin

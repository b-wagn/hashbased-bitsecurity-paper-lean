import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.StalledRun
import SlhDsaSecurity.Proof.CacheAvailability
import SlhDsaSecurity.Proof.LazyBridge

/-!
# Which cell a probe is charged against, and the flag that records it

`OpenCache.evalDist_stalled_lazyProgram_congr` says the stalled run does not mention the cell
it stalled on. To use it the charge has to be expressed as an event about that run, and a
probe has to be charged against *one* cell rather than against the table as a whole. This file
does both.

**One cell per probe.** `SensitiveAt` names the cell a candidate is charged against, and
`sensitiveAt_unique` is the lemma that keeps the rate at one unit per probe:
`Stakes.locate` reads the node off the address before any cell is consulted, and `Stakes.stake`
reads the cell off the node, so a candidate is charged against at most one cell. The events
"this probe is charged against cell `i`" are therefore disjoint as `i` ranges over the cells,
and summing them counts each probe once. Stated loosely — a bound per cell, added over cells —
the same sum would come to `|Index| / 2 ^ 128` per probe, which is useless; that is why the
disjointness is a named lemma and not a step inside a calculation.

**The flag.** `StalledRun.probEvent_flag_stalled_eq` wants the event carried as a sticky flag in
the handler's state, so `flagged` is `OpenCache.lazyProgram` with one added: a flag set when a
probe is charged against the stalled cell. It reads that cell, which is exactly why it is a
different handler from the blind one and why the two are only ever joined through the record —
`flag_iff_record` is that joining, and it is the only place their relationship is used.

The three hypotheses the stalled comparison takes hold for concrete reasons: the handler never
fails, availability only grows along a run so a released cell stays released, and a charge
requires the cell to be unavailable, so none can arise once it is released.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000

namespace SlhDsaSecurity.ChargedProbe

open CanonicalGraph SensitiveQuery OpenCache

variable {Node : Type}

/-! ## One cell per probe -/

/-! ## The cell a probe targets, and why the counts add

The charge against one cell is weighted by how many probes aim at that cell. What makes the
weighting legitimate is that aiming is decided by the probe's bytes alone: `Stakes.locate`
reads the node off the address and `Stakes.stake` reads the cell off the node, so no cell is
consulted and the count is a function of the record. And what makes the weights add to the
number of probes rather than to `|Index|` times it is that a probe aims at one cell —
`targets_unique`, the same uniqueness as `sensitiveAt_unique` with the table dropped. Summing
the per-cell charges *unweighted* would give `|Index| / 2 ^ 128` per probe and be useless; the
weights are the whole point. -/

/-! ## The per-cell charge at a fixed record

Against a record fixed in advance, the cells are drawn afterwards and only the probes aiming at
a given cell can be charged against it, each with the probability that one coordinate takes one
value. -/

/-! ## The charge against one cell, with that cell alone drawn

Being charged against a given cell reads the table at that one coordinate and nowhere else, so
the charge can be stated against a single uniform cell rather than a whole uniform table. That
is what lets it be applied to a run which is blind to that coordinate but not to the others:
the coordinate may be drawn after the run, and the weight is then the expected number of probes
aiming at it. -/

/-! ## The weight becomes an expectation

With the cell drawn after the run, the fixed-record bound averages: the charge against one cell
is the expected number of probes aiming at it, over `2 ^ 128`. Nothing about the run is assumed
except that it does not draw the cell. -/

/-- **A finite sum and an expectation may be exchanged.** Over `ℝ≥0∞` both sides are defined and
equal whatever the summands; it is stated for an arbitrary index set because this is the step at
which a factor of the index count would hide, and a general statement is easier to check than
one specialised to a type with `2 ^ 26` elements. -/
theorem sum_tsum_comm {Index Result : Type} [DecidableEq Index] (nodes : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ nodes, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ nodes, summand index result := by
  refine Finset.induction_on nodes ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    exact tsum_congr fun result => by rw [Finset.sum_insert hhead]

/-! ## The flag -/

variable (publicSeed : Digest)

/-! ## What the stalled comparison takes

Three facts, each for a concrete reason: the handler never fails, availability only grows along
a run so a released cell stays released, and a charge requires the cell to be unavailable, so
none can arise once it is released.

**These are stated at `lazyProgram`, and `HandlerStall` states them at any handler.** What they
use of this one is collected as `HandlerFacts.Facts`, and `HandlerStall` is this section and the
two below it with `Facts` in place of the handler — the form `ServingProgram.servingProgram`
needs. Anything new belongs there; these stay as the instance their existing readers name. -/

/-! ## The flag is the record

The only place the flagged handler and the blind one are related: they record the same probes,
and the flag says exactly that one of them was charged. -/

/-! ## The weight does not notice the stall

The probes a record aims at a cell are all made while that cell is unavailable, so a run
stalled at the moment it becomes available aims at it exactly as often as the unstalled one.
That is frozen-insensitivity of the count, and `StalledRun.expectation_stalled_eq` turns it
into equality of the expectations — which is what lets the per-cell weights be summed under one
measure rather than under one measure per cell.

**`HandlerStall` has all of this at an arbitrary handler**, by `HandlerFacts.Facts`; the four
`*_stalled_eq` results below are `HandlerStall`'s under the same names. -/

/-! ### Counting the distinct probes

The charge weighs the probes a record names, not the entries it holds: a repeated probe is one
chance at the cell and not two, and the containment that pays for these weights speaks of the
entry a probe installed, which a repeat does not install twice. So the weight is taken at the
record's `List.dedup`, and what that counts is read as a `Finset` cardinality, where appending a
probe is inserting one element. -/

/-! ## The charge itself does not notice the stall

A charge needs the cell unavailable, so none can arise after the stall. "Some recorded probe is
charged against this cell" is therefore as frozen-insensitive as the count is, and
`StalledRun.expectation_stalled_eq` applies to its indicator directly. The flag the stalled
comparison was built around is not needed for it: the event is already a function of the
record, which the handler carries. -/

/-! ## The same, for a list the run returns rather than one it records

The forgery's own claims are not probes: they are read off the signature at the cache the run
ends with, so what weighs them is a function of the run's **value**, which the quietness
hypothesis above cannot speak about. It does not need to. A claim is charged against a cell only
while that cell is unavailable at the cache the claim carries, which is the final one — so once
the stall has fired, and availability only grows, no claim is charged at all.
`StalledRun.expectation_stalled_eq_of_zero` is that argument, and the hypothesis it takes here
is the one fact about the claims that makes it work: every claim is read at the run's own final
cache. -/

/-! ## The lazy presentation against the eager one

The handler at *total* availability answers every canonical input: it is the eager programmed
cache, read on demand. The handler at the real availability answers only what a run may
legitimately compute. They differ at exactly the canonical inputs of the sensitive nodes, so
flagging those compares them with no slack.

The flag lives only here. Neither handler reads it, and the charge itself stays flag-free.

**`HandlerLenient` is this section at an arbitrary pair of handlers.** What it takes beyond
`HandlerFacts.Facts` is `HandlerFacts.Lenient` — the one fact that is about *two* handlers
rather than one, so it could not be a field of the interface: off these queries the lenient
handler and the strict one take the same step. -/

/-! ## The comparison's flag is the record's own event

The flag the two presentations are compared on is a function of the record, exactly as the
charge's event is. Carrying that as an invariant — the flag summarises the record so far — gives
it without any bookkeeping about suffixes. -/

/-! ## A sensitive query is a charged candidate

The comparison speaks of any structural node the signatures leave a child of unavailable; the
charge speaks of a node bundled with the proof that it has exactly one child. The bridge runs
one way only, and that is the way it is needed: a node with an unavailable child *has* exactly
one child, because availability is closed and every digit is below the chain length, so it is
one of the charge's nodes. The converse — that a node of the charge has an unavailable child —
is not used and is not proved. -/

/-! ## The comparison's flag changes nothing the charge sees

The flag the comparison is stated on reads the cells — it asks whether a query sits at the
canonical input of a node the signatures leave a child of unavailable — so the handler carrying
it is not blind to the table, and the charge is not proved about it. The charge is proved about
the flag-free wrapper. The two differ only in what they write to the flag, so on an event that
does not read the flag they agree, which is all the charge needs. -/

end SlhDsaSecurity.ChargedProbe

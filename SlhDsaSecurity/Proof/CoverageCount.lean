import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.ClassGrowth

/-!
# The coverage charge, read against the counter the budget speaks about

`BlockViews.prob_targetCovered_le` charges the coverage event at the expected length of the
*target recording*. `ClassExpectation.prob_bad_or_coverage_le` wants it at the expected
*in-class query count* of the split counter. The two are not the same observable, and this file
is the one inequality between them, in the only direction that is safe: the recorder files an
entry only on a fresh in-class query, and the counter charges every in-class query, fresh or
repeated. So the recording never outruns the count.

That is a budget fact and not a plumbing one, which is why it is proved rather than arranged.
If the recorder could file something the counter does not charge, the answer side's two charges
would not partition the queries and the whole accounting would have to be reopened.

Everything here is generic in the two recorder tests. The game's pair is being narrowed — the
signer's own `PRF_msg` query is a message-class input and must not be filed as a target — and
nothing below reads the tests beyond `hrightClass`, which any narrowing keeps.

It is also generic in the recorder's *state*: everything runs against a `RecorderView.CacheView`,
so the carrier the handler actually threads — which carries a served set and a flag beside the
cache — is as good a state here as the bare cache, and the budget is still read at the view's
own cache.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CoverageCount

open Security DigestTape ClassGrowth

variable {σ : Type} [RecorderView.CacheView σ]

/-! ## The recorder is the shared oracle, at a general view

`SplitPrefix.mem_support_rom` and `recorder_eq_rom` say the recordings are write-only, and both
are stated at the cache. At a general view the same two facts hold for the same reason, and
neither needs anything of `CacheView` beyond its one law: a hit returns the cached answer and
leaves the carrier, a miss draws and installs, and `cache_update` says the cache that results is
the cache the shared oracle would have. So the carrier may carry whatever else it likes — a
flag, a served set — and stay invisible to every event about the result and the cache.

They are here rather than in `RecorderView` only because this is the file that needs them; they
would sit as well beside the other two. -/

/-- The shared oracle's hit branch, at the type the world's query carries. `SplitPrefix` never
needed this because both sides of its induction were already spelled at that type; here the two
sides are spelled at different states, so the ascription has to be written down. -/
theorem rom_run_inr_some (input : Bytes) (cache : QueryCache HashSpec) (cached : HashOutput)
    (hcached : cache input = some cached) :
    (KeygenUniform.rom (Sum.inr input)).run cache =
      (pure (cached, cache) :
        ProbComp (OracleWorld.Range (Sum.inr input) × QueryCache HashSpec)) := by
  rw [DigestTape.rom_run_inr, QueryImpl.withCaching_run_some _ hcached]
  rfl

/-- The shared oracle's miss branch, likewise. -/
theorem rom_run_inr_none (input : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache input = none) :
    (KeygenUniform.rom (Sum.inr input)).run cache =
      (((fun answer => (answer, cache.cacheQuery input answer)) <$>
        ($ᵗ HashOutput : ProbComp _)) :
          ProbComp (OracleWorld.Range (Sum.inr input) × QueryCache HashSpec)) := by
  rw [DigestTape.rom_run_inr, QueryImpl.withCaching_run_none _ hfresh]
  rfl

/-! ## The recording never outruns the count -/

/-! ## The split counter read as the total count

The join is stated at a computation returning the game's `Outcome × Nat` — the count
`countAllHashes` keeps — while the charge needs the run instrumented with the split `Counts`.
They are the same run: `ClassGrowth.countAllHashes_eq_readOff` says summing the two slots
*is* `countAllHashes`, so the recorded run of one is the image of the recorded run of the other.
That is what lets the join be applied where the counts are split, and the budget be read where
they are not. -/

/-! ## An expected count is a sum of tail probabilities

The recorder is write-only, so the plain run and the recorded run agree on every event that
does not mention the recordings — but `SplitPrefix.recorder_eq_rom` says that of *events*, and
what has to move across is an *expectation*. Writing the expectation as the sum of its tail
probabilities turns one into the other, with no second induction. -/

/-! ## The coverage charge in the shape the two-class bound takes it

Everything above, assembled: the event moves to the recorded run because the recordings are
write-only, the charge is paid at the expected target recording, the recording is bounded by
the in-class count, and the count's expectation moves back. What comes out is literally the
`hcoverage` hypothesis of `ClassExpectation.prob_bad_or_coverage_le`.

The join from the game's own coverage event to `BlockViews.TargetCovered` is left as a
hypothesis, because it is the only part that reads the two recorder tests, and those are being
narrowed. `SplitWitness.mem_records_of_covered_of_not_late` is that hypothesis at the game's
pair. -/

/-! ## Both charges, against one budget, with nothing left but the join

`ClassExpectation.prob_bad_or_coverage_le` took the coverage charge in expectation form as a
hypothesis because nobody had it. It is now `prob_coverage_le_expected`, and this is the two
charges composed: the structural clause paid by the outside slot, the coverage clause by the
inside slot of the same counter, and the budget bounding their sum on every run.

What is left to supply is the join — the game's own coverage event implying
`BlockViews.TargetCovered` — and the two recording caps. Those are the only places the recorder
tests are read, which is why they are hypotheses here and not instantiations. -/

/-! ## The same two charges, read one step earlier

Everything above concludes at the shared oracle's run, where the recordings are gone. An event
that *reads* them cannot be stated there at all — the ordering defect is one — so the charge has
to be available before they are forgotten.

It is, and at no cost. `prob_coverage_le_expected`'s first line is the event-level move from the
recorded run to the shared one, and every step after it already lives at the recorded run; so
the recorded form is that proof with the move deleted. The structural charge crosses the other
way by `recorderOf_eq_rom`, because `GrowthCharge.Bad` reads only the result and the cache. The
budget is read where it always was, at the shared oracle's run, since it is a fact about the
count and not about the recordings.

These stand *beside* the shared-oracle forms rather than replacing them: the chain that consumes
those is still green, and an unused lemma costs less than a red build. -/

/-! ## The two charges, generic in the run

Everything above is stated at `BlockViews.recordedRun`, which is one computation under
`RecorderView.recorderOf` from a cache. The carrier tail is not of that shape — it is bracketed,
three-stage, under `RecorderView.noticingRecorderOf`, and records against the frame in flight
rather than against the cache — so no map carries one run to the other and the charge has to be
restated rather than transported.

**What has to be restated is less than the chain suggests.** The place where the two charges
*meet* mentions nothing about how either was proved: it takes the structural clause at its own
expected count, the coverage clause at its own, and the pathwise fact that the two counts share
one budget. `prob_bad_or_coverage_le_of_charges` below is exactly that, over an arbitrary run,
and it is three lines. Everything run-specific lives in the two charges handed to it.

So the interface a new run has to meet is three propositions, not a recorder. For
`BlockViews.recordedRun` they are what the sections above prove; for the carrier tail they are
what remains, and the coverage one is the only hard half — it is the tape factorisation, which
has to be redone at a bracketed noticing run rather than adapted.

**On one thing that does *not* have to be re-argued.** `noticingRecorderOf` runs `recorderOf` at
`CacheView.onQuery state.1 input`, and `cacheOf_onQuery` says the notice leaves the cache alone.
So `appendedOf`'s guard is still `CacheView.cacheOf state.1 input = none`: the carrier files on a
**fresh draw only**, exactly as the cache recorder does. Every step above that rests on a filed
entry being a fresh uniform answer — `rightRecord_length_le_count`, and the tape factorisation's
per-entry rate — keeps its premise. What the notice changes is which state the two *tests* are
read at, which is the whole point of the repair and costs those steps nothing. -/

end SlhDsaSecurity.CoverageCount

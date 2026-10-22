import SlhDsaSecurity.Proof.NoticingBlocks
import SlhDsaSecurity.Proof.CoverageCount

/-!
# The two charges at the recorder that notices

`CoverageCount` assembles the coverage charge against the counter the budget speaks about, at
`RecorderView.recorderOf`. This file is the same assembly at
`RecorderView.noticingRecorderOf`, so that the carrier's run can be handed to
`prob_bad_or_coverage_le_of_charges` on the same terms the cache run is.

**The two inductions are the only things here that are proofs rather than compositions**, and
both are the cache version with the `inr` head rewritten and the noticed carrier named. The
reason they survive is the one `CoverageCount`'s own closing section records: `noticingRecorderOf`
runs `recorderOf` at `CacheView.onQuery state.1 input`, and `cacheOf_onQuery` leaves the cache
alone, so `appendedOf`'s guard is still freshness at the same cache. **An entry is still filed
on a fresh draw only**, which is the premise every counting and rate step rests on. What the
notice changes is which state the two *tests* are read at, and no step here reads them.

What is **not** carried, because it does not mention a recorder:
`tsum_probOutput_mul_count`, and the two meeting points
`prob_bad_or_coverage_le_of_two_charges` and `prob_bad_or_coverage_le_of_charges`, which are
already generic in the run and take this file's conclusions as they stand.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.NoticingCoverage

open Security DigestTape ClassGrowth NoticingTape NoticingBlocks CoverageCount

variable {σ : Type} [RecorderView.CacheView σ]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A recorded run at a view is a run of the shared oracle**, at the view's own cache. -/
theorem mem_support_rom_of_noticingRecorderOf {α : Type}
    (leftKeep rightKeep : Bytes → σ → Prop) (computation : OracleComp OracleWorld α)
    (state : RecorderView.StateOf σ) (result : α × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
      computation).run state)) :
    (result.1, RecorderView.CacheView.cacheOf result.2.1) ∈
      support ((simulateQ KeygenUniform.rom computation).run
        (RecorderView.CacheView.cacheOf state.1)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    refine ⟨(step.1, RecorderView.CacheView.cacheOf step.2.1), ?_,
      ih step.1 step.2 result hrest⟩
    rcases queried with coin | input
    · rw [RecorderView.noticingRecorderOf_run_inl, RecorderView.recorderOf_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨value, hvalue, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [DigestTape.rom_run_inl, mem_support_bind_iff]
      refine ⟨value, hvalue, ?_⟩
      rw [support_pure, Set.mem_singleton_iff, hpure]
    · cases hcached : RecorderView.CacheView.cacheOf state.1 input with
      | some cached =>
        rw [RecorderView.noticingRecorderOf_run_inr_some _ _ input state cached hcached,
          support_pure,
          Set.mem_singleton_iff] at hstep
        rw [rom_run_inr_some input _ cached hcached, support_pure,
          Set.mem_singleton_iff, hstep, RecorderView.cacheOf_onQuery]
      | none =>
        rw [RecorderView.noticingRecorderOf_run_inr_none _ _ input state hcached,
          support_map] at hstep
        obtain ⟨answer, hanswer, hpair⟩ := hstep
        rw [rom_run_inr_none input _ hcached, support_map]
        refine ⟨answer, hanswer, ?_⟩
        rw [← hpair]
        refine congrArg _ ?_
        rw [RecorderView.CacheView.cache_update, RecorderView.cacheOf_onQuery]

/-! ## The recording never outruns the count -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The target recording never outruns the in-class count.** An entry is filed only on a
*fresh* query whose input the counter charges, so each entry has its own unit of the inside
slot. -/
theorem noticingRightRecord_length_le_count
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : RecorderView.StateOf σ)
      (result : (α × Counts) × RecorderView.StateOf σ),
      result ∈ support ((simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
        (countQueries (splitCost inClass inside outside) computation)).run state) →
      result.2.2.2.length ≤ state.2.2.length + result.1.2 inside := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    rw [hmem]
    simp
  | query_bind queried next ih =>
    intro state result hmem
    rw [WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, hshape⟩ := hrest
    have hcount : result.1.2 inside =
        (splitCost inClass inside outside queried) inside + inner.1.2 inside := by
      rw [← hshape]; rfl
    have hrecords : result.2 = inner.2 := by rw [← hshape]
    have hih := ih step.1 step.2 inner hinner
    have hstepRecord : step.2.2.2.length ≤
        state.2.2.length + (splitCost inClass inside outside queried) inside := by
      rcases queried with coin | input
      · rw [RecorderView.noticingRecorderOf_run_inl] at hstep
        rw [RecorderView.recorderOf_step_inl leftKeep rightKeep coin state step hstep]
        simp
      · rw [RecorderView.noticingRecorderOf_run_inr] at hstep
        rw [RecorderView.recorderOf_step_record leftKeep rightKeep input
            (RecorderView.CacheView.onQuery state.1 input, state.2) step hstep,
          RecorderView.appendedOf]
        split_ifs with hfiledLeft hfiledRight
        · simp
        · rw [splitCost_inside inClass inside outside input
            (hrightClass input (RecorderView.CacheView.onQuery state.1 input) hfiledRight.2)]
          simp
        · simp
    rw [hrecords, hcount]
    omega

/-! ## The split counter read as the total count

The join is stated at a computation returning the game's `Outcome × Nat` — the count
`countAllHashes` keeps — while the charge needs the run instrumented with the split `Counts`.
They are the same run: `ClassGrowth.countAllHashes_eq_readOff` says summing the two slots
*is* `countAllHashes`, so the recorded run of one is the image of the recorded run of the other.
That is what lets the join be applied where the counts are split, and the budget be read where
they are not. -/

open scoped Classical in
/-- **A split-counted recorded run is a total-counted one.** -/
theorem mem_support_noticingRecorder_countAllHashes
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
      (countQueries (splitCost inClass inside outside) computation)).run state)) :
    ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) ∈
      support ((simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
        (countAllHashes computation)).run state) := by
  classical
  rw [← countAllHashes_eq_readOff (splitCost inClass inside outside)
      (fun counts => counts inside + counts outside) rfl (splitSum_add inside outside)
      (splitCost_add_eq_hashCost inClass hne) computation,
    simulateQ_map, StateT.run_map, support_map]
  exact ⟨result, hmem, rfl⟩

open scoped Classical in
/-- **The in-class count is inside the budget.** The two slots add to the run's own hash count,
the recordings are invisible to it, and the budget bounds it — so the inside slot alone is
bounded, which is the cap the target recording needs. -/
theorem noticingInside_le_of_budget
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
      (countQueries (splitCost inClass inside outside) computation)).run state))
    (budget : Nat)
    (hbudget : ∀ plain ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf state.1)),
      plain.1.2 ≤ budget) :
    result.1.2 inside ≤ budget := by
  have htotal := mem_support_rom_of_noticingRecorderOf leftKeep rightKeep
    (countAllHashes computation)
    state _ (mem_support_noticingRecorder_countAllHashes leftKeep rightKeep inClass hne computation
      state result hmem)
  have hle : result.1.2 inside + result.1.2 outside ≤ budget := hbudget _ htotal
  omega

open scoped Classical in
/-- **The target recording is inside the budget**, which is the cap the charge needs — and a cap
on the *count*, not on the charge: the charge stays an expectation in the entries actually
filed. -/
theorem noticingRightRecord_length_le_budget
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support (noticingRecordedRun leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache))
    (budget : Nat)
    (hbudget : ∀ plain ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf cache)),
      plain.1.2 ≤ budget) :
    result.2.2.2.length ≤ budget := by
  have hcount := noticingRightRecord_length_le_count leftKeep rightKeep inClass inside outside
    hrightClass computation (cache, [], []) result hmem
  have hinside := noticingInside_le_of_budget leftKeep rightKeep inClass hne computation
    (cache, [], []) result hmem budget hbudget
  simp only [List.length_nil, Nat.zero_add] at hcount
  omega

open scoped Classical in
/-- **An expected count moves across the recording.** The recordings are write-only, so a count
read off the result alone has the same expectation on the recorded run as on the plain one. -/
theorem expectedCount_noticingRecorder_eq_rom
    (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (count : α → Nat) :
    (∑' result, Pr[= result | (simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep)
        computation).run state] * ((count result.1 : Nat) : ℝ≥0∞)) =
      ∑' result, Pr[= result | (simulateQ KeygenUniform.rom computation).run
          (RecorderView.CacheView.cacheOf state.1)] *
        ((count result.1 : Nat) : ℝ≥0∞) := by
  classical
  rw [tsum_probOutput_mul_count, tsum_probOutput_mul_count]
  refine tsum_congr fun index => ?_
  exact noticingRecorderOf_eq_rom leftKeep rightKeep computation state
    (fun plain => index < count plain.1)

/-! ## The coverage charge in the shape the two-class bound takes it

Everything above, assembled: the event moves to the recorded run because the recordings are
write-only, the charge is paid at the expected target recording, the recording is bounded by
the in-class count, and the count's expectation moves back. What comes out is literally the
`hcoverage` hypothesis of `ClassExpectation.prob_bad_or_coverage_le`.

The join from the game's own coverage event to `BlockViews.TargetCovered` is left as a
hypothesis, because it is the only part that reads the two recorder tests, and those are being
narrowed. `SplitWitness.mem_records_of_covered_of_not_late` is that hypothesis at the game's
pair. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The coverage charge, against the counter the budget speaks about.** One unit of `2 ^ -141`
and one unit of `2 ^ -128` per *expected* in-class query — which is the inside slot of the same
counter whose outside slot pays for the structural charge, so the two add against one budget. -/
theorem prob_noticingCoverage_le_expected
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (coverage : (α × Counts) × QueryCache HashSpec → Prop)
    (hjoin : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      coverage (result.1, RecorderView.CacheView.cacheOf result.2.1) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[coverage | (simulateQ KeygenUniform.rom
        (countQueries (splitCost inClass inside outside) computation)).run
          (RecorderView.CacheView.cacheOf cache)] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        ClassExpectation.expected ((simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run
              (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [← noticingRecorderOf_eq_rom leftKeep rightKeep
    (countQueries (splitCost inClass inside outside) computation) (cache, [], []) coverage]
  refine le_trans (le_trans (probEvent_mono hjoin)
    (prob_noticingTargetCovered_le leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache leftLength rightLength
      hcap hleftBound hrightBound)) (add_le_add le_rfl (ENNReal.div_le_div_right ?_ _))
  calc (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞))
      ≤ ∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep
            (countQueries (splitCost inClass inside outside) computation) cache] *
          (((result.1.2 inside : Nat)) : ℝ≥0∞) := by
        refine ClassExpectation.expected_mono _ _ _ fun result hmem => ?_
        have hcount := noticingRightRecord_length_le_count leftKeep rightKeep inClass inside outside
          hrightClass computation (cache, [], []) result hmem
        simpa using hcount
    _ = ClassExpectation.expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run
            (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) :=
        expectedCount_noticingRecorder_eq_rom leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) (cache, [], [])
          (fun value => value.2 inside)

/-! ## Both charges, against one budget, with nothing left but the join

`ClassExpectation.prob_bad_or_coverage_le` took the coverage charge in expectation form as a
hypothesis because nobody had it. It is now `prob_noticingCoverage_le_expected`, and this is the two
charges composed: the structural clause paid by the outside slot, the coverage clause by the
inside slot of the same counter, and the budget bounding their sum on every run.

What is left to supply is the join — the game's own coverage event implying
`BlockViews.TargetCovered` — and the two recording caps. Those are the only places the recorder
tests are read, which is why they are hypotheses here and not instantiations. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half, with one budget and no coverage hypothesis.** -/
theorem prob_bad_or_coverage_le_of_join_noticing
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (leftKeep rightKeep : Bytes → σ → Prop)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : σ)
    (hclean : GrowthCharge.CleanBad bad (RecorderView.CacheView.cacheOf initialCache))
    (coverage : (α × Nat) × QueryCache HashSpec → Prop)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hjoin : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      coverage ((result.1.1, result.1.2 inside + result.1.2 outside),
          RecorderView.CacheView.cacheOf result.2.1) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf initialCache)),
      result.1.2 ≤ budget) :
    Pr[fun result : (α × Nat) × QueryCache HashSpec =>
        GrowthCharge.Bad bad result ∨ coverage result |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run
          (RecorderView.CacheView.cacheOf initialCache)] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine ClassExpectation.prob_bad_or_coverage_le inClass hne bad hrate hbadClass computation
    (RecorderView.CacheView.cacheOf initialCache) hclean coverage ((1 : ℝ≥0∞) / 2 ^ 141) ?_
    budget hbudget
  rw [ClassGrowth.probEvent_splitCost inClass hne computation
    (RecorderView.CacheView.cacheOf initialCache) coverage]
  exact prob_noticingCoverage_le_expected leftKeep rightKeep inClass inside outside hrightClass
    computation initialCache leftLength rightLength hcap _ hjoin hleftBound hrightBound

/-! ## The same two charges, read one step earlier

Everything above concludes at the shared oracle's run, where the recordings are gone. An event
that *reads* them cannot be stated there at all — the ordering defect is one — so the charge has
to be available before they are forgotten.

It is, and at no cost. `prob_noticingCoverage_le_expected`'s first line is the event-level move
from the
recorded run to the shared one, and every step after it already lives at the recorded run; so
the recorded form is that proof with the move deleted. The structural charge crosses the other
way by `noticingRecorderOf_eq_rom`, because `GrowthCharge.Bad` reads only the result and the
cache. The
budget is read where it always was, at the shared oracle's run, since it is a fact about the
count and not about the recordings.

These stand *beside* the shared-oracle forms rather than replacing them: the chain that consumes
those is still green, and an unused lemma costs less than a red build. -/

open scoped Classical in
/-- **The split counter is the total count, at the recorded run.** The recorder answers the two
instrumentations identically — it never reads the value — so the same map that collapses the two
slots collapses the two recorded runs. -/
theorem noticingRecordedRun_splitCost_eq_map (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ) :
    (fun result : (α × Counts) × RecorderView.StateOf σ =>
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) <$>
        noticingRecordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache =
      noticingRecordedRun leftKeep rightKeep (countAllHashes computation) cache := by
  classical
  rw [noticingRecordedRun, noticingRecordedRun,
    ← countAllHashes_eq_readOff (splitCost inClass inside outside)
      (fun counts => counts inside + counts outside) rfl (splitSum_add inside outside)
      (splitCost_add_eq_hashCost inClass hne) computation,
    simulateQ_map, StateT.run_map]

open scoped Classical in
/-- **An event at the total count, read at the split one.** -/
theorem probEvent_splitCost_noticingRecorded (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (event : (α × Nat) × RecorderView.StateOf σ → Prop) :
    Pr[event | noticingRecordedRun leftKeep rightKeep (countAllHashes computation) cache] =
      Pr[fun result : (α × Counts) × RecorderView.StateOf σ =>
          event ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) |
        noticingRecordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] := by
  rw [← noticingRecordedRun_splitCost_eq_map leftKeep rightKeep inClass hne computation cache,
    probEvent_map]
  rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The coverage charge at the recorded run**, where an event may still read the recordings.
The join is the only thing that changes shape: its coverage event is now a predicate on the
whole recorded result, so a conjunct about the recordings may ride along inside it. -/
theorem prob_noticingCoverage_le_expected_recorded
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (coverage : (α × Counts) × RecorderView.StateOf σ → Prop)
    (hjoin : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      coverage result → BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[coverage | noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        ClassExpectation.expected ((simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run
              (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (le_trans (probEvent_mono hjoin)
    (prob_noticingTargetCovered_le leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache leftLength rightLength
      hcap hleftBound hrightBound)) (add_le_add le_rfl (ENNReal.div_le_div_right ?_ _))
  calc (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞))
      ≤ ∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep
            (countQueries (splitCost inClass inside outside) computation) cache] *
          (((result.1.2 inside : Nat)) : ℝ≥0∞) := by
        refine ClassExpectation.expected_mono _ _ _ fun result hmem => ?_
        have hcount := noticingRightRecord_length_le_count leftKeep rightKeep inClass inside outside
          hrightClass computation (cache, [], []) result hmem
        simpa using hcount
    _ = ClassExpectation.expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run
            (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) :=
        expectedCount_noticingRecorder_eq_rom leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) (cache, [], [])
          (fun value => value.2 inside)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, at the recorded run.** Same budget, same two slots, same
bound; what is new is only where the conclusion is read, which is early enough for the coverage
clause to mention the recordings. -/
theorem prob_bad_or_coverage_le_of_join_noticingRecorded
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (leftKeep rightKeep : Bytes → σ → Prop)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : σ)
    (hclean : GrowthCharge.CleanBad bad (RecorderView.CacheView.cacheOf initialCache))
    (coverage : (α × Nat) × RecorderView.StateOf σ → Prop)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hjoin : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      coverage ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf initialCache)),
      result.1.2 ≤ budget) :
    Pr[fun result : (α × Nat) × RecorderView.StateOf σ =>
        GrowthCharge.Bad bad (result.1, RecorderView.CacheView.cacheOf result.2.1) ∨
          coverage result |
        noticingRecordedRun leftKeep rightKeep (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine ClassExpectation.add_le_of_shared_budget_const
    ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run
        (RecorderView.CacheView.cacheOf initialCache))
    _ _ ((1 : ℝ≥0∞) / 2 ^ 141) (fun result => (result.1.2) outside)
    (fun result => (result.1.2) inside) budget ?_ ?_ ?_
  · rw [noticingRecordedRun,
      noticingRecorderOf_eq_rom leftKeep rightKeep (countAllHashes computation)
        (initialCache, [], [])
        (GrowthCharge.Bad bad), ← mul_one_div]
    exact ClassExpectation.prob_bad_le_expected_outside inClass hne bad _ hrate hbadClass
      computation (RecorderView.CacheView.cacheOf initialCache) hclean
  · rw [probEvent_splitCost_noticingRecorded leftKeep rightKeep inClass hne computation
      initialCache
      coverage]
    exact prob_noticingCoverage_le_expected_recorded leftKeep rightKeep inClass inside outside
      hrightClass computation initialCache leftLength rightLength hcap _ hjoin hleftBound
      hrightBound
  · intro result hmem
    have hplain : result.1.2 inside + result.1.2 outside ≤ budget :=
      hbudget _ (mem_support_countAllHashes_of_splitCost inClass hne computation
        (RecorderView.CacheView.cacheOf initialCache) result hmem)
    omega


end SlhDsaSecurity.NoticingCoverage

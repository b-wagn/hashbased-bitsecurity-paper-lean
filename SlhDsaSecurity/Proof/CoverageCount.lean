import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.ClassExpectation

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

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A recorded run at a view is a run of the shared oracle**, at the view's own cache. -/
theorem mem_support_rom_of_recorderOf {α : Type}
    (leftKeep rightKeep : Bytes → σ → Prop) (computation : OracleComp OracleWorld α)
    (state : RecorderView.StateOf σ) (result : α × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf leftKeep rightKeep)
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
    · rw [RecorderView.recorderOf_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, hvalue, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [DigestTape.rom_run_inl, mem_support_bind_iff]
      refine ⟨value, hvalue, ?_⟩
      rw [support_pure, Set.mem_singleton_iff, hpure]
    · cases hcached : RecorderView.CacheView.cacheOf state.1 input with
      | some cached =>
        rw [RecorderView.recorderOf_run_inr_some _ _ input state cached hcached, support_pure,
          Set.mem_singleton_iff] at hstep
        rw [rom_run_inr_some input _ cached hcached, support_pure, Set.mem_singleton_iff,
          hstep]
      | none =>
        rw [RecorderView.recorderOf_run_inr_none _ _ input state hcached, support_map] at hstep
        obtain ⟨answer, hanswer, hpair⟩ := hstep
        rw [rom_run_inr_none input _ hcached, support_map]
        refine ⟨answer, hanswer, ?_⟩
        rw [← hpair]
        exact congrArg _ (RecorderView.CacheView.cache_update state.1 input answer).symm

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The recordings are invisible**, at a general view: an event about the result and the view's
cache has the same probability under the recorded run as under the shared oracle's. -/
theorem recorderOf_eq_rom {α : Type}
    (leftKeep rightKeep : Bytes → σ → Prop) (computation : OracleComp OracleWorld α)
    (state : RecorderView.StateOf σ) (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result : α × RecorderView.StateOf σ =>
        event (result.1, RecorderView.CacheView.cacheOf result.2.1) |
      (simulateQ (RecorderView.recorderOf leftKeep rightKeep) computation).run state] =
      Pr[event | (simulateQ KeygenUniform.rom computation).run
        (RecorderView.CacheView.cacheOf state.1)] := by
  classical
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · rw [RecorderView.recorderOf_run_inl, DigestTape.rom_run_inl, bind_assoc, bind_assoc]
      simp only [pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      exact tsum_congr fun value => by rw [ih value state]
    · cases hcached : RecorderView.CacheView.cacheOf state.1 input with
      | some cached =>
        rw [RecorderView.recorderOf_run_inr_some _ _ input state cached hcached,
          rom_run_inr_some input _ cached hcached]
        simp only [pure_bind]
        exact ih cached (state.1, RecorderView.appendedOf leftKeep rightKeep input state cached)
      | none =>
        rw [RecorderView.recorderOf_run_inr_none _ _ input state hcached,
          rom_run_inr_none input _ hcached]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        refine tsum_congr fun answer => ?_
        rw [← RecorderView.CacheView.cache_update state.1 input answer]
        exact congrArg _ (ih answer (RecorderView.CacheView.update state.1 input answer,
          RecorderView.appendedOf leftKeep rightKeep input state answer))

/-! ## The recording never outruns the count -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The target recording never outruns the in-class count.** An entry is filed only on a
*fresh* query whose input the counter charges, so each entry has its own unit of the inside
slot. -/
theorem rightRecord_length_le_count
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : RecorderView.StateOf σ)
      (result : (α × Counts) × RecorderView.StateOf σ),
      result ∈ support ((simulateQ (RecorderView.recorderOf leftKeep rightKeep)
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
      · rw [RecorderView.recorderOf_step_inl leftKeep rightKeep coin state step hstep]
        simp
      · rw [RecorderView.recorderOf_step_record leftKeep rightKeep input state step hstep,
          RecorderView.appendedOf]
        split_ifs with hfiledLeft hfiledRight
        · simp
        · rw [splitCost_inside inClass inside outside input
            (hrightClass input state.1 hfiledRight.2)]
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
theorem mem_support_recorder_countAllHashes
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf leftKeep rightKeep)
      (countQueries (splitCost inClass inside outside) computation)).run state)) :
    ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) ∈
      support ((simulateQ (RecorderView.recorderOf leftKeep rightKeep)
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
theorem inside_le_of_budget
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support ((simulateQ (RecorderView.recorderOf leftKeep rightKeep)
      (countQueries (splitCost inClass inside outside) computation)).run state))
    (budget : Nat)
    (hbudget : ∀ plain ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf state.1)),
      plain.1.2 ≤ budget) :
    result.1.2 inside ≤ budget := by
  have htotal := mem_support_rom_of_recorderOf leftKeep rightKeep (countAllHashes computation)
    state _ (mem_support_recorder_countAllHashes leftKeep rightKeep inClass hne computation
      state result hmem)
  have hle : result.1.2 inside + result.1.2 outside ≤ budget := hbudget _ htotal
  omega

open scoped Classical in
/-- **The target recording is inside the budget**, which is the cap the charge needs — and a cap
on the *count*, not on the charge: the charge stays an expectation in the entries actually
filed. -/
theorem rightRecord_length_le_budget
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (result : (α × Counts) × RecorderView.StateOf σ)
    (hmem : result ∈ support (BlockViews.recordedRun leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache))
    (budget : Nat)
    (hbudget : ∀ plain ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf cache)),
      plain.1.2 ≤ budget) :
    result.2.2.2.length ≤ budget := by
  have hcount := rightRecord_length_le_count leftKeep rightKeep inClass inside outside
    hrightClass computation (cache, [], []) result hmem
  have hinside := inside_le_of_budget leftKeep rightKeep inClass hne computation
    (cache, [], []) result hmem budget hbudget
  simp only [List.length_nil, Nat.zero_add] at hcount
  omega

/-! ## An expected count is a sum of tail probabilities

The recorder is write-only, so the plain run and the recorded run agree on every event that
does not mention the recordings — but `SplitPrefix.recorder_eq_rom` says that of *events*, and
what has to move across is an *expectation*. Writing the expectation as the sum of its tail
probabilities turns one into the other, with no second induction. -/

open scoped Classical in
/-- A finite count's expectation is the sum of its tail probabilities. -/
theorem tsum_probOutput_mul_count {β : Type} (run : ProbComp β) (count : β → Nat) :
    ∑' value, Pr[= value | run] * ((count value : Nat) : ℝ≥0∞) =
      ∑' index : Nat, Pr[fun value => index < count value | run] := by
  classical
  have hlayer : ∀ value : β, Pr[= value | run] * ((count value : Nat) : ℝ≥0∞) =
      ∑' index : Nat, (if index < count value then Pr[= value | run] else 0) := by
    intro value
    rw [tsum_eq_sum (s := Finset.range (count value))
      (fun index hindex => if_neg (by simpa using hindex))]
    rw [Finset.sum_congr rfl (fun index hindex =>
      if_pos (Finset.mem_range.mp hindex)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_comm]
  calc ∑' value, Pr[= value | run] * ((count value : Nat) : ℝ≥0∞)
      = ∑' value, ∑' index : Nat, (if index < count value then Pr[= value | run] else 0) :=
        tsum_congr hlayer
    _ = ∑' index : Nat, ∑' value, (if index < count value then Pr[= value | run] else 0) :=
        ENNReal.tsum_comm
    _ = ∑' index : Nat, Pr[fun value => index < count value | run] :=
        tsum_congr fun index => (probEvent_eq_tsum_ite _ _).symm

open scoped Classical in
/-- **An expected count moves across the recording.** The recordings are write-only, so a count
read off the result alone has the same expectation on the recorded run as on the plain one. -/
theorem expectedCount_recorder_eq_rom
    (leftKeep rightKeep : Bytes → σ → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (state : RecorderView.StateOf σ)
    (count : α → Nat) :
    (∑' result, Pr[= result | (simulateQ (RecorderView.recorderOf leftKeep rightKeep)
        computation).run state] * ((count result.1 : Nat) : ℝ≥0∞)) =
      ∑' result, Pr[= result | (simulateQ KeygenUniform.rom computation).run
          (RecorderView.CacheView.cacheOf state.1)] *
        ((count result.1 : Nat) : ℝ≥0∞) := by
  classical
  rw [tsum_probOutput_mul_count, tsum_probOutput_mul_count]
  refine tsum_congr fun index => ?_
  exact recorderOf_eq_rom leftKeep rightKeep computation state
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
theorem prob_coverage_le_expected
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (coverage : (α × Counts) × QueryCache HashSpec → Prop)
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      coverage (result.1, RecorderView.CacheView.cacheOf result.2.1) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
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
  rw [← recorderOf_eq_rom leftKeep rightKeep
    (countQueries (splitCost inClass inside outside) computation) (cache, [], []) coverage]
  refine le_trans (le_trans (probEvent_mono hjoin)
    (BlockViews.prob_targetCovered_le leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache leftLength rightLength
      hcap hleftBound hrightBound)) (add_le_add le_rfl (ENNReal.div_le_div_right ?_ _))
  calc (∑' result, Pr[= result | BlockViews.recordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞))
      ≤ ∑' result, Pr[= result | BlockViews.recordedRun leftKeep rightKeep
            (countQueries (splitCost inClass inside outside) computation) cache] *
          (((result.1.2 inside : Nat)) : ℝ≥0∞) := by
        refine ClassExpectation.expected_mono _ _ _ fun result hmem => ?_
        have hcount := rightRecord_length_le_count leftKeep rightKeep inClass inside outside
          hrightClass computation (cache, [], []) result hmem
        simpa using hcount
    _ = ClassExpectation.expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run
            (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) :=
        expectedCount_recorder_eq_rom leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) (cache, [], [])
          (fun value => value.2 inside)

/-! ## Both charges, against one budget, with nothing left but the join

`ClassExpectation.prob_bad_or_coverage_le` took the coverage charge in expectation form as a
hypothesis because nobody had it. It is now `prob_coverage_le_expected`, and this is the two
charges composed: the structural clause paid by the outside slot, the coverage clause by the
inside slot of the same counter, and the budget bounding their sum on every run.

What is left to supply is the join — the game's own coverage event implying
`BlockViews.TargetCovered` — and the two recording caps. Those are the only places the recorder
tests are read, which is why they are hypotheses here and not instantiations. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half, with one budget and no coverage hypothesis.** -/
theorem prob_bad_or_coverage_le_of_join
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
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      coverage ((result.1.1, result.1.2 inside + result.1.2 outside),
          RecorderView.CacheView.cacheOf result.2.1) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
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
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine ClassExpectation.prob_bad_or_coverage_le inClass hne bad hrate hbadClass computation
    (RecorderView.CacheView.cacheOf initialCache) hclean coverage ((1 : ℝ≥0∞) / 2 ^ 141) ?_
    budget hbudget
  rw [ClassGrowth.probEvent_splitCost inClass hne computation
    (RecorderView.CacheView.cacheOf initialCache) coverage]
  exact prob_coverage_le_expected leftKeep rightKeep inClass inside outside hrightClass
    computation initialCache leftLength rightLength hcap _ hjoin hleftBound hrightBound

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

open scoped Classical in
/-- **The split counter is the total count, at the recorded run.** The recorder answers the two
instrumentations identically — it never reads the value — so the same map that collapses the two
slots collapses the two recorded runs. -/
theorem recordedRun_splitCost_eq_map (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ) :
    (fun result : (α × Counts) × RecorderView.StateOf σ =>
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) <$>
        BlockViews.recordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache =
      BlockViews.recordedRun leftKeep rightKeep (countAllHashes computation) cache := by
  classical
  rw [BlockViews.recordedRun, BlockViews.recordedRun,
    ← countAllHashes_eq_readOff (splitCost inClass inside outside)
      (fun counts => counts inside + counts outside) rfl (splitSum_add inside outside)
      (splitCost_add_eq_hashCost inClass hne) computation,
    simulateQ_map, StateT.run_map]

open scoped Classical in
/-- **An event at the total count, read at the split one.** -/
theorem probEvent_splitCost_recorded (leftKeep rightKeep : Bytes → σ → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (event : (α × Nat) × RecorderView.StateOf σ → Prop) :
    Pr[event | BlockViews.recordedRun leftKeep rightKeep (countAllHashes computation) cache] =
      Pr[fun result : (α × Counts) × RecorderView.StateOf σ =>
          event ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) |
        BlockViews.recordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] := by
  rw [← recordedRun_splitCost_eq_map leftKeep rightKeep inClass hne computation cache,
    probEvent_map]
  rfl

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The coverage charge at the recorded run**, where an event may still read the recordings.
The join is the only thing that changes shape: its coverage event is now a predicate on the
whole recorded result, so a conjunct about the recordings may ride along inside it. -/
theorem prob_coverage_le_expected_recorded
    (leftKeep rightKeep : Bytes → σ → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (coverage : (α × Counts) × RecorderView.StateOf σ → Prop)
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      coverage result → BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[coverage | BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        ClassExpectation.expected ((simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run
              (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (le_trans (probEvent_mono hjoin)
    (BlockViews.prob_targetCovered_le leftKeep rightKeep
      (countQueries (splitCost inClass inside outside) computation) cache leftLength rightLength
      hcap hleftBound hrightBound)) (add_le_add le_rfl (ENNReal.div_le_div_right ?_ _))
  calc (∑' result, Pr[= result | BlockViews.recordedRun leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞))
      ≤ ∑' result, Pr[= result | BlockViews.recordedRun leftKeep rightKeep
            (countQueries (splitCost inClass inside outside) computation) cache] *
          (((result.1.2 inside : Nat)) : ℝ≥0∞) := by
        refine ClassExpectation.expected_mono _ _ _ fun result hmem => ?_
        have hcount := rightRecord_length_le_count leftKeep rightKeep inClass inside outside
          hrightClass computation (cache, [], []) result hmem
        simpa using hcount
    _ = ClassExpectation.expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run
            (RecorderView.CacheView.cacheOf cache))
          (fun result => (result.1.2) inside) :=
        expectedCount_recorder_eq_rom leftKeep rightKeep
          (countQueries (splitCost inClass inside outside) computation) (cache, [], [])
          (fun value => value.2 inside)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, at the recorded run.** Same budget, same two slots, same
bound; what is new is only where the conclusion is read, which is early enough for the coverage
clause to mention the recordings. -/
theorem prob_bad_or_coverage_le_of_join_recorded
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
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      coverage ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run (RecorderView.CacheView.cacheOf initialCache)),
      result.1.2 ≤ budget) :
    Pr[fun result : (α × Nat) × RecorderView.StateOf σ =>
        GrowthCharge.Bad bad (result.1, RecorderView.CacheView.cacheOf result.2.1) ∨
          coverage result |
        BlockViews.recordedRun leftKeep rightKeep (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine ClassExpectation.add_le_of_shared_budget_const
    ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run
        (RecorderView.CacheView.cacheOf initialCache))
    _ _ ((1 : ℝ≥0∞) / 2 ^ 141) (fun result => (result.1.2) outside)
    (fun result => (result.1.2) inside) budget ?_ ?_ ?_
  · rw [BlockViews.recordedRun,
      recorderOf_eq_rom leftKeep rightKeep (countAllHashes computation) (initialCache, [], [])
        (GrowthCharge.Bad bad), ← mul_one_div]
    exact ClassExpectation.prob_bad_le_expected_outside inClass hne bad _ hrate hbadClass
      computation (RecorderView.CacheView.cacheOf initialCache) hclean
  · rw [probEvent_splitCost_recorded leftKeep rightKeep inClass hne computation initialCache
      coverage]
    exact prob_coverage_le_expected_recorded leftKeep rightKeep inClass inside outside
      hrightClass computation initialCache leftLength rightLength hcap _ hjoin hleftBound
      hrightBound
  · intro result hmem
    have hplain : result.1.2 inside + result.1.2 outside ≤ budget :=
      hbudget _ (mem_support_countAllHashes_of_splitCost inClass hne computation
        (RecorderView.CacheView.cacheOf initialCache) result hmem)
    omega

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

open scoped Classical in
/-- **Where the two charges meet, with nothing in it at all.** Two events, two counts, one
budget: the first event at its own expected count, the second at its own with a constant beside
it, and the two counts inside one budget on every supported run.

There is no recorder here, no state, no `Counts`, and no `σ` — the run is an arbitrary
`ProbComp β`. That is the whole interface a new presentation has to meet for the answer half's
bound to be taken at it, and it is three lines, because the place where two charges meet cannot
see how either was proved.

**It cannot spend concentration margin.** It adds two expectations and a constant; nothing in it
is a tail bound. Whatever margin the factorisation has is still there afterwards. -/
theorem prob_bad_or_coverage_le_of_two_charges {β : Type}
    (run : ProbComp β) (first second : β → Prop) (constant : ℝ≥0∞)
    (firstCount secondCount : β → Nat) (budget : Nat)
    (hfirst : Pr[first | run] ≤
      ClassExpectation.expected run firstCount / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsecond : Pr[second | run] ≤
      constant + ClassExpectation.expected run secondCount / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hshare : ∀ value ∈ support run, firstCount value + secondCount value ≤ budget) :
    Pr[fun value => first value ∨ second value | run] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + constant :=
  le_trans (probEvent_or_le _ _ _)
    (ClassExpectation.add_le_of_shared_budget_const run _ _ constant firstCount secondCount
      budget hfirst hsecond hshare)

open scoped Classical in
/-- **Where the two charges meet, with no recorder in sight.** The structural clause at its own
expected count, the coverage clause at its own with a constant beside it, and one budget bounding
their sum on every supported run.

This is the interface a run has to meet for the answer half's bound to be taken at it. -/
theorem prob_bad_or_coverage_le_of_charges {α : Type} {σ : Type} [RecorderView.CacheView σ]
    (bad : Bytes → HashOutput → Prop) (inside outside : QueryKind)
    (run : ProbComp ((α × Counts) × RecorderView.StateOf σ))
    (coverage : (α × Counts) × RecorderView.StateOf σ → Prop) (constant : ℝ≥0∞)
    (hstructural : Pr[fun result => GrowthCharge.Bad bad
          (((result.1.1, result.1.2 inside + result.1.2 outside) :
            α × Nat), RecorderView.CacheView.cacheOf result.2.1) | run] ≤
      ClassExpectation.expected run (fun result => result.1.2 outside) /
        ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hcoverage : Pr[coverage | run] ≤
      constant + ClassExpectation.expected run (fun result => result.1.2 inside) /
        ((2 ^ 128 : Nat) : ℝ≥0∞))
    (budget : Nat)
    (hshare : ∀ result ∈ support run,
      result.1.2 outside + result.1.2 inside ≤ budget) :
    Pr[fun result => GrowthCharge.Bad bad
          (((result.1.1, result.1.2 inside + result.1.2 outside) : α × Nat),
            RecorderView.CacheView.cacheOf result.2.1) ∨ coverage result | run] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + constant := by
  classical
  refine le_trans (probEvent_or_le _ _ _) ?_
  exact ClassExpectation.add_le_of_shared_budget_const run _ _ constant
    (fun result => result.1.2 outside) (fun result => result.1.2 inside) budget
    hstructural hcoverage hshare

end SlhDsaSecurity.CoverageCount

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
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CoverageCount

open Security DigestTape ClassGrowth

/-! ## The recording never outruns the count -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The target recording never outruns the in-class count.** An entry is filed only on a
*fresh* query whose input the counter charges, so each entry has its own unit of the inside
slot. -/
theorem rightRecord_length_le_count
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : SplitPrefix.SplitState)
      (result : (α × Counts) × SplitPrefix.SplitState),
      result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
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
      · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
        obtain ⟨value, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure]
        simp
      · rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure]
        show (SplitPrefix.appended leftKeep rightKeep input state answer.1).2.length ≤ _
        rw [SplitPrefix.appended]
        split_ifs with hfiledLeft hfiledRight
        · simp
        · rw [splitCost_inside inClass inside outside input
            (hrightClass input state.1 hfiledRight.2)]
          simp
        · simp
    rw [hrecords, hcount]
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
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (state : SplitPrefix.SplitState)
    (count : α → Nat) :
    (∑' result, Pr[= result | (simulateQ (SplitPrefix.recorder leftKeep rightKeep)
        computation).run state] * ((count result.1 : Nat) : ℝ≥0∞)) =
      ∑' result, Pr[= result | (simulateQ KeygenUniform.rom computation).run state.1] *
        ((count result.1 : Nat) : ℝ≥0∞) := by
  classical
  rw [tsum_probOutput_mul_count, tsum_probOutput_mul_count]
  refine tsum_congr fun index => ?_
  exact SplitPrefix.recorder_eq_rom leftKeep rightKeep computation state
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
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) (inClass : Bytes → Prop)
    (inside outside : QueryKind)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (coverage : (α × Counts) × QueryCache HashSpec → Prop)
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      coverage (result.1, result.2.1) → BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[coverage | (simulateQ KeygenUniform.rom
        (countQueries (splitCost inClass inside outside) computation)).run cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        ClassExpectation.expected ((simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run cache)
          (fun result => (result.1.2) inside) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [← SplitPrefix.recorder_eq_rom leftKeep rightKeep
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
          (countQueries (splitCost inClass inside outside) computation)).run cache)
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
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (hrightClass : ∀ input cache, rightKeep input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (coverage : (α × Nat) × QueryCache HashSpec → Prop)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hjoin : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      coverage ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (BlockViews.recordedRun leftKeep rightKeep
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (α × Nat) × QueryCache HashSpec =>
        GrowthCharge.Bad bad result ∨ coverage result |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine ClassExpectation.prob_bad_or_coverage_le inClass hne bad hrate hbadClass computation
    initialCache hclean coverage ((1 : ℝ≥0∞) / 2 ^ 141) ?_ budget hbudget
  rw [ClassGrowth.probEvent_splitCost inClass hne computation initialCache coverage]
  exact prob_coverage_le_expected leftKeep rightKeep inClass inside outside hrightClass
    computation initialCache leftLength rightLength hcap _ hjoin hleftBound hrightBound

end SlhDsaSecurity.CoverageCount

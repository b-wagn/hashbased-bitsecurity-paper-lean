import SlhDsaSecurity.Proof.NoticingTape
import SlhDsaSecurity.Proof.BlockViews

/-!
# The coverage charge at the recorder that notices

`BlockViews` proves the coverage charge at `RecorderView.recorderOf`. The carrier's repair runs
`RecorderView.noticingRecorderOf`, and `NoticingTape` carries the whole tape factorisation and
the leave-one-out charge to it. This file is the composition on top: the same two charges, at
the same two rates, at the repaired recorder.

**Nothing here is new mathematics and that is the point.** Every step is the `BlockViews` step
with `splitTapeRecorder` replaced by `noticingSplitTapeRecorder` and `recorderOf` by
`noticingRecorderOf`; the pieces that do not mention a recorder at all —
`covered_of_recordCovers`, `prob_not_goodBlock_le`, `prob_blockHit_le`, `tsum_probOutput_map` —
are cited from `BlockViews` rather than copied, because the notice cannot see them.

The two length hypotheses, the `2 ^ -141` and the per-entry `2 ^ -128` are unchanged, so the
margins recorded in `REVIEW.md` are the same numbers at this recorder.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.NoticingBlocks

open DigestTape TapeFactor NoticingTape BlockViews

variable {σ : Type} [RecorderView.CacheView σ]


/-- The run itself, with both recordings and no blocks. -/
noncomputable def noticingRecordedRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ) :
    ProbComp (α × RecorderView.StateOf σ) :=
  (simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep) computation).run (cache, ([], []))

/-- **The event the game supplies.** Some recorded target digest has its fourteen FORS leaves
all supplied by the disclosing recording. -/
def TargetCovered {α : Type} (result : α × RecorderView.StateOf σ) : Prop :=
  ∃ entry ∈ result.2.2.2, RecordCovers result.2.2.1 (MessageDigest.parse entry.2)

/-- The blocked run, read as the recorded run. -/
theorem evalDist_noticingRecordedRun_eq (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) :
    𝒟[noticingRecordedRun leftKeep rightKeep computation cache] =
      𝒟[(fun outcome :
          (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
          TapeFactor.forgetSplit outcome.2) <$>
        noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] := by
  rw [noticingRecordedRun, evalDist_noticingSplitTapeRun leftKeep rightKeep computation leftLength
    rightLength cache [] [], noticingBlockRun]
  simp only [map_bind, Functor.map_map]

/-- A supported outcome of the blocked run is a supported run against its own two blocks. -/
theorem mem_support_noticingBlockRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat)
    (outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ))
    (hmem : outcome ∈ support (noticingBlockRun leftKeep rightKeep computation cache
      leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧
      outcome.1.2 ∈ support (padding rightLength) ∧
        outcome.2 ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
          computation).run (cache, (outcome.1.1, outcome.1.2), ([], []))) := by
  rw [noticingBlockRun, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleftTape, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hrightTape, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨result, hresult, hshape⟩ := hinner
  rw [← hshape]
  exact ⟨hleftTape, hrightTape, hresult⟩

/-- The blocked run never fails once its blocks are drawn. -/
theorem noticingBlockRun_tail_neverFails (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftTape : List HashOutput) (rightLength : Nat) :
    Pr[⊥ | padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$>
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), ([], []))] = 0 := by
  refine probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨padding_neverFails rightLength,
    fun rightTape _ => ?_⟩
  rw [map_eq_bind_pure_comp]
  exact probFailure_bind_eq_zero_iff _ _ |>.mpr
    ⟨noticingSplitTapeRun_neverFails leftKeep rightKeep computation _, fun _ _ => by simp⟩

open scoped Classical in
/-- **The disclosing block's own law.** An event about it alone is an event about the block
draw, which is what lets the concentration bound be read at the blocked run. -/
theorem noticingProb_leftBlock (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (event : List HashOutput → Prop) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
        event outcome.1.1 |
      noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] =
      Pr[event | padding leftLength] := by
  classical
  rw [noticingBlockRun, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun leftTape => ?_
  have hshape : ∀ outcome ∈ support (padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$>
          (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), ([], []))),
      outcome.1.1 = leftTape := by
    intro outcome hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨rightTape, -, hinner⟩ := hmem
    rw [support_map] at hinner
    obtain ⟨result, -, hbuilt⟩ := hinner
    rw [← hbuilt]
  rw [probEvent_congr' (fun outcome hmem => by rw [hshape outcome hmem]) rfl,
    probEvent_const, noticingBlockRun_tail_neverFails leftKeep rightKeep computation cache leftTape
      rightLength, tsub_zero]
  split <;> simp

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The coverage charge, at the recorded run.** One unit of `2 ^ -141` for the disclosing
block's concentration, and one unit of `2 ^ -128` per *expected* target recorded — never per
target the budget allows. -/
theorem prob_noticingTargetCovered_le (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep computation cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep computation
      cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[TargetCovered | noticingRecordedRun leftKeep rightKeep computation cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  set reshape : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) →
      α × RecorderView.StateOf σ := fun outcome => TapeFactor.forgetSplit outcome.2 with hreshape
  have hlaw := evalDist_noticingRecordedRun_eq leftKeep rightKeep computation cache leftLength
    rightLength
  have hsupport : support (noticingRecordedRun leftKeep rightKeep computation cache) =
      support (reshape <$> noticingBlockRun leftKeep rightKeep computation cache leftLength
        rightLength) := Averaging.support_eq_of_evalDist_eq hlaw
  -- The event, moved to the blocked run.
  have hevent : Pr[TargetCovered | noticingRecordedRun leftKeep rightKeep computation cache] =
      Pr[fun outcome => TargetCovered (reshape outcome) |
        noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] := by
    rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
    rfl
  -- The expectation, moved to the blocked run.
  have hexpect : (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation
        cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
      ∑' outcome, Pr[= outcome |
          noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((TapeFactor.rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
    rw [show (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' result, Pr[= result | reshape <$> noticingBlockRun leftKeep rightKeep computation
          cache leftLength rightLength] * ((result.2.2.2.length : Nat) : ℝ≥0∞) from
      tsum_congr fun result => by rw [probOutput_def, probOutput_def, hlaw]]
    haveI : DecidableEq (α × RecorderView.StateOf σ) := Classical.decEq _
    exact tsum_probOutput_map _ reshape _
  rw [hevent, hexpect]
  -- The game's event implies the charge's, once the block is good.
  refine le_trans (probEvent_mono (q := fun outcome =>
      (¬ GoodBlock leftLength outcome.1.1) ∨
        ∃ index : Fin rightLength, index.val < (TapeFactor.rightOf outcome.2.2).length ∧
          GoodBlock leftLength outcome.1.1 ∧
          ∃ value, outcome.1.2[index.val]? = some value ∧
            BlockHit leftLength outcome.1.1 value) ?_) ?_
  · rintro outcome hmem ⟨entry, hentry, hcovers⟩
    by_cases hgood : GoodBlock leftLength outcome.1.1
    · refine Or.inr ?_
      obtain ⟨hleftTape, hrightTape, hrun⟩ := mem_support_noticingBlockRun leftKeep rightKeep
        computation cache leftLength rightLength outcome hmem
      have hplain : reshape outcome ∈
          support (noticingRecordedRun leftKeep rightKeep computation cache) := by
        rw [hsupport, support_map]
        exact ⟨outcome, hmem, rfl⟩
      obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hentry
      have hrightLen : (TapeFactor.rightOf outcome.2.2).length ≤ rightLength :=
        hrightBound _ hplain
      have hleftLen : (TapeFactor.leftOf outcome.2.2).length ≤ leftLength :=
        hleftBound _ hplain
      have hcellRight := noticingRightOf_getElem? leftKeep rightKeep computation cache
        outcome.1.1 outcome.1.2 [] [] outcome.2 hrun index
        (by simp only [List.length_nil, Nat.zero_add]; exact hindex)
        (by rw [padding_length rightLength outcome.1.2 hrightTape]
            exact lt_of_lt_of_le hindex hrightLen)
      refine ⟨⟨index, lt_of_lt_of_le hindex hrightLen⟩,
        show index < (TapeFactor.rightOf outcome.2.2).length from hindex, hgood, entry.2, ?_, ?_⟩
      · have hcell : ((TapeFactor.rightOf outcome.2.2)[index]?).map Prod.snd =
            outcome.1.2[index]? := by
          simp only [List.length_nil, Nat.zero_add] at hcellRight
          exact hcellRight
        have hget : (TapeFactor.rightOf outcome.2.2)[index]? = some entry := by
          rw [List.getElem?_eq_getElem (show index < (TapeFactor.rightOf outcome.2.2).length
            from hindex)]
          exact congrArg some (show (TapeFactor.rightOf outcome.2.2)[index] = entry from hvalue)
        rw [← hcell, hget]
        rfl
      · refine covered_of_recordCovers leftLength outcome.1.1 (TapeFactor.leftOf outcome.2.2)
          (MessageDigest.parse entry.2) (fun position hposition => ?_) hleftLen ?_
        · have := noticingLeftOf_getElem? leftKeep rightKeep computation cache outcome.1.1
            outcome.1.2 [] [] outcome.2 hrun position
            (by simp only [List.length_nil, Nat.zero_add]; exact hposition)
            (by rw [padding_length leftLength outcome.1.1 hleftTape]
                exact lt_of_lt_of_le hposition hleftLen)
          simp only [List.length_nil, Nat.zero_add] at this
          exact this
        · exact hcovers
    · exact Or.inl hgood
  · refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ ?_)
    · rw [noticingProb_leftBlock leftKeep rightKeep computation cache leftLength rightLength
        (fun block => ¬ GoodBlock leftLength block)]
      exact prob_not_goodBlock_le leftLength hcap
    · rw [← mul_one_div]
      exact noticingProb_exists_hit_le_expected leftKeep rightKeep computation cache
        leftLength rightLength (GoodBlock leftLength) (BlockHit leftLength) _
        (fun block hgood => prob_blockHit_le leftLength block hgood)


end SlhDsaSecurity.NoticingBlocks

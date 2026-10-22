import SlhDsaSecurity.Proof.BlockViews
import SlhDsaSecurity.Proof.NoticingTape

/-!
# The coverage charge at the recorder that notices

`BlockViews.prob_targetCovered_le` charges the coverage event at the expected length of the
target recording, through two blocks drawn in advance. `NoticingTape` has the whole tape layer
beneath it at `RecorderView.noticingRecorderOf` — the factorisation, the causality, the two
cell-for-cell readings and the leave-one-out charge — with the same statements and the same
absence of hypotheses. This file is the layer above the line, where the game's own FORS events
live: `GoodBlock`, `BlockHit`, `RecordCovers`, `TargetCovered`.

**Nothing about the argument changes, and that is the point.** The notice moves which state the
two *tests* are read at; it moves neither the freshness guard that decides when a cell is filed
nor the rate a filed cell is charged at. So what is summed is still the target recording, the
per-cell factor is still a fresh uniform answer, and the margin downstream is the number it was.
Every proof here is `BlockViews`' with four names changed.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.NoticingBlockViews

open Security DigestTape BlockViews

variable {σ : Type} [RecorderView.CacheView σ]

/-- The two-recording run at the recorder that notices. -/
noncomputable def noticingRecordedRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ) :
    ProbComp (α × RecorderView.StateOf σ) :=
  (simulateQ (RecorderView.noticingRecorderOf leftKeep rightKeep) computation).run
    (cache, ([], []))

open scoped Classical in
/-- **The recorded run is the blocked run, forgotten.** `NoticingTape`'s factorisation,
read at the two-recording run this file charges. -/
theorem evalDist_noticingRecordedRun_eq (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) :
    𝒟[noticingRecordedRun leftKeep rightKeep computation cache] =
      𝒟[(fun outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
          TapeFactor.forgetSplit outcome.2) <$>
        NoticingTape.noticingBlockRun leftKeep rightKeep computation cache leftLength
          rightLength] := by
  rw [noticingRecordedRun, NoticingTape.evalDist_noticingSplitTapeRun leftKeep rightKeep
    computation leftLength rightLength cache [] [], NoticingTape.noticingBlockRun]
  simp only [map_bind, Functor.map_map]

/-- A supported outcome of the blocked run is a supported run against its own two blocks. -/
theorem mem_support_noticingBlockRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat)
    (outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ))
    (hmem : outcome ∈ support (NoticingTape.noticingBlockRun leftKeep rightKeep computation cache
      leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧
      outcome.1.2 ∈ support (padding rightLength) ∧
        outcome.2 ∈ support ((simulateQ (NoticingTape.noticingSplitTapeRecorder leftKeep rightKeep)
          computation).run (cache, (outcome.1.1, outcome.1.2), ([], []))) := by
  rw [NoticingTape.noticingBlockRun, mem_support_bind_iff] at hmem
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
          (simulateQ (NoticingTape.noticingSplitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), ([], []))] = 0 := by
  refine probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨padding_neverFails rightLength,
    fun rightTape _ => ?_⟩
  rw [map_eq_bind_pure_comp]
  exact probFailure_bind_eq_zero_iff _ _ |>.mpr
    ⟨NoticingTape.noticingSplitTapeRun_neverFails leftKeep rightKeep computation _, fun _ _ => by simp⟩

open scoped Classical in
/-- **The disclosing block's own law.** An event about it alone is an event about the block
draw, which is what lets the concentration bound be read at the blocked run. -/
theorem prob_leftBlock (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (event : List HashOutput → Prop) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
        event outcome.1.1 |
      NoticingTape.noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] =
      Pr[event | padding leftLength] := by
  classical
  rw [NoticingTape.noticingBlockRun, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun leftTape => ?_
  have hshape : ∀ outcome ∈ support (padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$>
          (simulateQ (NoticingTape.noticingSplitTapeRecorder leftKeep rightKeep) computation).run
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

open scoped Classical in
/-- Expectations move through a reshaping of the outcome. -/
theorem tsum_probOutput_map {β γ : Type} [DecidableEq γ] (run : ProbComp β) (reshape : β → γ)
    (weight : γ → ℝ≥0∞) :
    ∑' value, Pr[= value | reshape <$> run] * weight value =
      ∑' value, Pr[= value | run] * weight (reshape value) := by
  classical
  calc ∑' value, Pr[= value | reshape <$> run] * weight value
      = ∑' value, (∑' source, if value = reshape source then Pr[= source | run] else 0) *
          weight value :=
        tsum_congr fun value => by rw [probOutput_map_eq_tsum_ite]
    _ = ∑' value, ∑' source,
          (if value = reshape source then Pr[= source | run] else 0) * weight value :=
        tsum_congr fun value => ENNReal.tsum_mul_right.symm
    _ = ∑' source, ∑' value,
          (if value = reshape source then Pr[= source | run] else 0) * weight value :=
        ENNReal.tsum_comm
    _ = ∑' source, Pr[= source | run] * weight (reshape source) :=
        tsum_congr fun source => by
          rw [tsum_eq_single (reshape source)
            (fun other hother => by rw [if_neg hother, zero_mul]), if_pos rfl]

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
    (hrightBound : ∀ result ∈ support (noticingRecordedRun leftKeep rightKeep computation cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[TargetCovered | noticingRecordedRun leftKeep rightKeep computation cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  set reshape : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) →
      α × RecorderView.StateOf σ := fun outcome => TapeFactor.forgetSplit outcome.2 with hreshape
  have hlaw := evalDist_noticingRecordedRun_eq leftKeep rightKeep computation cache leftLength rightLength
  have hsupport : support (noticingRecordedRun leftKeep rightKeep computation cache) =
      support (reshape <$> NoticingTape.noticingBlockRun leftKeep rightKeep computation cache leftLength
        rightLength) := Averaging.support_eq_of_evalDist_eq hlaw
  -- The event, moved to the blocked run.
  have hevent : Pr[TargetCovered | noticingRecordedRun leftKeep rightKeep computation cache] =
      Pr[fun outcome => TargetCovered (reshape outcome) |
        NoticingTape.noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] := by
    rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
    rfl
  -- The expectation, moved to the blocked run.
  have hexpect : (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
      ∑' outcome, Pr[= outcome |
          NoticingTape.noticingBlockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((TapeFactor.rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
    rw [show (∑' result, Pr[= result | noticingRecordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' result, Pr[= result | reshape <$> NoticingTape.noticingBlockRun leftKeep rightKeep computation
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
      have hcellRight := NoticingTape.noticingRightOf_getElem? leftKeep rightKeep computation cache
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
        · have := NoticingTape.noticingLeftOf_getElem? leftKeep rightKeep computation cache outcome.1.1
            outcome.1.2 [] [] outcome.2 hrun position
            (by simp only [List.length_nil, Nat.zero_add]; exact hposition)
            (by rw [padding_length leftLength outcome.1.1 hleftTape]
                exact lt_of_lt_of_le hposition hleftLen)
          simp only [List.length_nil, Nat.zero_add] at this
          exact this
        · exact hcovers
    · exact Or.inl hgood
  · refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ ?_)
    · rw [prob_leftBlock leftKeep rightKeep computation cache leftLength rightLength
        (fun block => ¬ GoodBlock leftLength block)]
      exact prob_not_goodBlock_le leftLength hcap
    · rw [← mul_one_div]
      exact NoticingTape.noticingProb_exists_hit_le_expected leftKeep rightKeep computation cache
        leftLength rightLength (GoodBlock leftLength) (BlockHit leftLength) _
        (fun block hgood => prob_blockHit_le leftLength block hgood)

end SlhDsaSecurity.NoticingBlockViews

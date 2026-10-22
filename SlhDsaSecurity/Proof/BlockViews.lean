import SlhDsaSecurity.Proof.TapeFactor
import SlhDsaSecurity.Proof.Averaging

/-!
# A block of answers, read as a tape of parsed views

`TapeFactor` hands the coverage charge two blocks of `List HashOutput`, drawn by
`DigestTape.padding`, and takes the block predicate and the hit relation as parameters. The FORS
machinery states everything about `ForsDisclosureTape.Tape n = Fin n → View` instead. This file
is the one conversion between the two, and the two instances of those parameters that the game
needs: the block's loads concentrate, and a fresh answer is rarely covered by a block whose
loads are good.

The conversion is done once, here, rather than at each of the places downstream that would
otherwise each do it their own way.

`DigestTape.viewTape_uniform` already says a uniform *word* parses to a uniform tape. What is
missing is that `padding` draws a uniform word at all — it draws one answer at a time — and that
is `evalDist_padding_eq_ofFn`, by splitting a uniform function type at its first coordinate.

Nothing here needs `BlockDisclosures`. Its index split exists to make the disclosure set a
function of a fixed range of one tape; with the two roles on two separately drawn blocks the
disclosure set is a function of the whole of one of them, which is the same property held more
simply. What is used is the concentration bound and the single-coordinate coverage rate, each of
which is already stated at a tape of its own.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BlockViews

open DigestTape TapeFactor

/-! ## A block is a uniform word -/

/-- Uniform sampling of a pair is two independent draws. -/
theorem uniformSample_prod_eq_bind {α β : Type} [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let left ← $ᵗ α; let right ← $ᵗ β; pure (left, right)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-- Consing one answer onto a word is a bijection from the pair. -/
theorem cons_bijective (length : Nat) :
    Function.Bijective (fun pair : HashOutput × (Fin length → HashOutput) =>
      Fin.cons pair.1 pair.2 : HashOutput × (Fin length → HashOutput) →
        Fin (length + 1) → HashOutput) := by
  constructor
  · intro left right hsame
    have hhead := congrFun hsame 0
    have htail : ∀ index : Fin length, left.2 index = right.2 index := fun index => by
      have := congrFun hsame index.succ
      simpa using this
    exact Prod.ext (by simpa using hhead) (funext htail)
  · intro word
    exact ⟨(word 0, Fin.tail word), Fin.cons_self_tail word⟩

/-- **A block of independent draws is a uniform word.** `padding` draws one answer at a time;
the FORS machinery wants a function off `Fin length`. They agree. -/
theorem evalDist_padding_eq_ofFn (length : Nat) :
    𝒟[padding length] =
      𝒟[List.ofFn <$> ($ᵗ (Fin length → HashOutput) :
        ProbComp (Fin length → HashOutput))] := by
  induction length with
  | zero =>
    rw [padding, show (List.ofFn : (Fin 0 → HashOutput) → List HashOutput) =
        fun _ => ([] : List HashOutput) from by funext word; simp, map_eq_bind_pure_comp]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm
  | succ remaining ih =>
    have hbijection : 𝒟[(fun pair : HashOutput × (Fin remaining → HashOutput) =>
          Fin.cons pair.1 pair.2) <$>
        ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)] =
        𝒟[($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] :=
      evalDist_map_bijective_uniform_cross
        (α := HashOutput × (Fin remaining → HashOutput))
        (β := Fin (remaining + 1) → HashOutput) _ (cons_bijective remaining)
    calc 𝒟[padding (remaining + 1)]
        = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _)] := rfl
      _ = 𝒟[($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            (List.ofFn <$> ($ᵗ (Fin remaining → HashOutput) : ProbComp _)) >>= fun rest =>
              (pure (value :: rest) : ProbComp _)] := by
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun value => ?_
          rw [evalDist_bind, evalDist_bind, ih]
      _ = 𝒟[(fun pair : HashOutput × (Fin remaining → HashOutput) =>
              pair.1 :: List.ofFn pair.2) <$>
            ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)] := by
          rw [uniformSample_prod_eq_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      _ = 𝒟[List.ofFn <$> ($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] := by
          have hmap : 𝒟[List.ofFn <$>
                ((fun pair : HashOutput × (Fin remaining → HashOutput) =>
                  Fin.cons pair.1 pair.2) <$>
                    ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _))] =
              𝒟[List.ofFn <$> ($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _)] := by
            rw [evalDist_map, hbijection, evalDist_map]
          refine Eq.trans ?_ hmap
          rw [Functor.map_map]
          refine congrArg evalDist (congrArg (fun step =>
            step <$> ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)) ?_)
          funext pair
          simp [List.ofFn_succ]

/-! ## The block as a tape -/

/-- **A fresh answer parses to a uniform view.** -/
theorem evalDist_parse_uniform :
    𝒟[MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ MessageDigest.View : ProbComp MessageDigest.View)] := by
  have hsplit : 𝒟[MessageDigest.split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ (MessageDigest.View × (BitVec 2 × BitVec 7)) : ProbComp _)] :=
    evalDist_map_bijective_uniform_cross (α := HashOutput)
      (β := MessageDigest.View × (BitVec 2 × BitVec 7))
      MessageDigest.split MessageDigest.split_bijective
  calc 𝒟[MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)]
      = 𝒟[Prod.fst <$> (MessageDigest.split <$> ($ᵗ HashOutput : ProbComp HashOutput))] := by
        rw [Functor.map_map]
        rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (MessageDigest.View × (BitVec 2 × BitVec 7)) : ProbComp _)] := by
        rw [evalDist_map, hsplit, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- A block of answers, read as a tape of parsed FORS views. Cells past the block's end read as
a default, which never happens where the charge looks: it reads cell `index` only when the run
recorded an answer there. -/
def blockTape (length : Nat) (block : List HashOutput) : ForsDisclosureTape.Tape length :=
  fun index => MessageDigest.parse (block.getD index.val default)

/-- **A drawn block is a uniform tape.** -/
theorem evalDist_blockTape (length : Nat) :
    𝒟[blockTape length <$> padding length] =
      𝒟[($ᵗ (ForsDisclosureTape.Tape length) :
        ProbComp (ForsDisclosureTape.Tape length))] := by
  calc 𝒟[blockTape length <$> padding length]
      = 𝒟[blockTape length <$>
          (List.ofFn <$> ($ᵗ (Fin length → HashOutput) : ProbComp _))] := by
        rw [evalDist_map, evalDist_padding_eq_ofFn length, ← evalDist_map]
    _ = 𝒟[(fun word index => MessageDigest.parse (word index)) <$>
          ($ᵗ (Fin length → HashOutput) : ProbComp _)] := by
        rw [Functor.map_map]
        refine congrArg evalDist (congrArg (fun step =>
          step <$> ($ᵗ (Fin length → HashOutput) : ProbComp _)) ?_)
        funext word
        funext index
        simp [blockTape, List.getD_eq_getElem?_getD]
    _ = _ := viewTape_uniform length

/-! ## The two instances the game needs -/

/-- The block's loads are small enough for the single-coordinate coverage rate. -/
def GoodBlock (length : Nat) (block : List HashOutput) : Prop :=
  ∑ part, ForsDisclosureTape.loads (blockTape length block) part ^ 14 ≤ 2 ^ 103

/-- An answer whose fourteen FORS leaves are all disclosed by the block. -/
def BlockHit (length : Nat) (block : List HashOutput) (value : HashOutput) : Prop :=
  ForsCoverage.Covered (ForsDisclosureTape.disclosures (blockTape length block))
    (MessageDigest.parse value)

open scoped Classical in
/-- **The block's loads concentrate**, at the cap the FORS counting needs. This is the whole of
the `2 ^ -141` the coverage charge spends. -/
theorem prob_not_goodBlock_le (length : Nat) (hlength : length ≤ 5 * 2 ^ 62) :
    Pr[fun block => ¬ GoodBlock length block | padding length] ≤ (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  have hevent : Pr[fun block => ¬ GoodBlock length block | padding length] =
      Pr[fun tape => 2 ^ 103 < ∑ part, ForsDisclosureTape.loads tape part ^ 14 |
        ($ᵗ (ForsDisclosureTape.Tape length) :
          ProbComp (ForsDisclosureTape.Tape length))] := by
    rw [← probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_blockTape length), probEvent_map]
    exact probEvent_congr' (fun block _ => by
      simp only [Function.comp_def, GoodBlock, not_le]) rfl
  rw [hevent]
  exact ForsDisclosureTape.bad_load_probability length hlength

/-- **A fresh answer is rarely covered by a good block.** One unit of `2 ^ -128`, which is the
rate the per-cell charge is paid at. -/
theorem prob_blockHit_le (length : Nat) (block : List HashOutput)
    (hgood : GoodBlock length block) :
    Pr[fun value => BlockHit length block value | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (le_of_eq ?_) (ForsCoverage.fresh_coverage_le_of_loads
    (ForsDisclosureTape.disclosures (blockTape length block))
    (ForsDisclosureTape.loads (blockTape length block))
    (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree) hgood)
  rw [← probEvent_congr' (fun _ _ => Iff.rfl) evalDist_parse_uniform, probEvent_map]
  rfl

/-! ## From the recording's own witnesses to the block's disclosures

The game's coverage event is witnessed by entries of the *recording*; the charge reads the
disclosures off the whole *block*, the part no query reached included. Taking the block is only
ever an over-count — more disclosures make coverage likelier, so the charge is still an upper
bound — and the step that makes it one is this: an entry of the recording is a cell of the
block, so the leaf it supplies is a leaf the block discloses.

What this needs of the run is `TapeFactor.leftOf_getElem?` and that the recording did not
outrun its block. The second is a cap on the number of *disclosing* queries, which the signing
limit gives; it is not a cap on the targets, and the charge is still an expectation in those. -/

/-- A view all of whose fourteen leaves are supplied by entries of a recording, at the
recording's own FORS instance. This is the shape the game's coverage events are stated in. -/
def RecordCovers (record : DigestTape.Record) (view : MessageDigest.View) : Prop :=
  ∀ tree, ∃ entry ∈ record, (MessageDigest.parse entry.2).1 = view.1 ∧
    (MessageDigest.parse entry.2).2 tree = view.2 tree

open scoped Classical in
/-- **A recording's witnesses are the block's disclosures.** -/
theorem covered_of_recordCovers (length : Nat) (block : List HashOutput)
    (record : DigestTape.Record) (view : MessageDigest.View)
    (hcells : ∀ index : Nat, index < record.length →
      ((record[index]?).map Prod.snd) = block[index]?)
    (hlength : record.length ≤ length)
    (hcovers : RecordCovers record view) :
    ForsCoverage.Covered (ForsDisclosureTape.disclosures (blockTape length block)) view := by
  classical
  intro tree
  obtain ⟨entry, hmember, hinstance, hleaf⟩ := hcovers tree
  obtain ⟨index, hindex, hentry⟩ := List.mem_iff_getElem.mp hmember
  have hcell : block.getD index default = entry.2 := by
    have hread : ((record[index]?).map Prod.snd) = block[index]? := hcells index hindex
    rw [List.getElem?_eq_getElem hindex, hentry] at hread
    rw [List.getD_eq_getElem?_getD, ← hread]
    rfl
  have hview : blockTape length block ⟨index, lt_of_lt_of_le hindex hlength⟩ =
      MessageDigest.parse entry.2 := by
    rw [blockTape, hcell]
  rw [ForsDisclosureTape.disclosures]
  refine Finset.mem_image.mpr ⟨⟨index, lt_of_lt_of_le hindex hlength⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hview]
    exact hinstance
  · rw [hview]
    exact hleaf

variable {σ : Type} [RecorderView.CacheView σ]

/-! ## The coverage charge at the recorded run

The charge is proved at `TapeFactor.blockRun`, which carries the two blocks beside the result.
The game supplies a run that carries neither. `TapeFactor.evalDist_splitTapeRun` says the two are
the same law, so the event and the expectation both move across, and what is left is to read the
game's event — a target digest covered by the disclosing *recording* — as the charge's event, a
block cell hit by the disclosing *block*. That is the two cell correspondences and
`covered_of_recordCovers`.

The two length hypotheses are caps on *counts*, not on charges. The disclosing one is the
signing limit and is what the `2 ^ -141` is bought with; the target one is the query budget and
buys nothing — it only says the run cannot read past its block, and the charge stays an
expectation in the number of cells it did read. -/

/-- The run itself, with both recordings and no blocks. -/
noncomputable def recordedRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ) :
    ProbComp (α × RecorderView.StateOf σ) :=
  (simulateQ (RecorderView.recorderOf leftKeep rightKeep) computation).run (cache, ([], []))

/-- **The event the game supplies.** Some recorded target digest has its fourteen FORS leaves
all supplied by the disclosing recording. -/
def TargetCovered {α : Type} (result : α × RecorderView.StateOf σ) : Prop :=
  ∃ entry ∈ result.2.2.2, RecordCovers result.2.2.1 (MessageDigest.parse entry.2)

/-- The blocked run, read as the recorded run. -/
theorem evalDist_recordedRun_eq (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) :
    𝒟[recordedRun leftKeep rightKeep computation cache] =
      𝒟[(fun outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
          TapeFactor.forgetSplit outcome.2) <$>
        TapeFactor.blockRun leftKeep rightKeep computation cache leftLength rightLength] := by
  rw [recordedRun, TapeFactor.evalDist_splitTapeRun leftKeep rightKeep computation leftLength
    rightLength cache [] [], TapeFactor.blockRun]
  simp only [map_bind, Functor.map_map]

/-- A supported outcome of the blocked run is a supported run against its own two blocks. -/
theorem mem_support_blockRun (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat)
    (outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ))
    (hmem : outcome ∈ support (TapeFactor.blockRun leftKeep rightKeep computation cache
      leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧
      outcome.1.2 ∈ support (padding rightLength) ∧
        outcome.2 ∈ support ((simulateQ (TapeFactor.splitTapeRecorder leftKeep rightKeep)
          computation).run (cache, (outcome.1.1, outcome.1.2), ([], []))) := by
  rw [TapeFactor.blockRun, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleftTape, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hrightTape, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨result, hresult, hshape⟩ := hinner
  rw [← hshape]
  exact ⟨hleftTape, hrightTape, hresult⟩

/-- The blocked run never fails once its blocks are drawn. -/
theorem blockRun_tail_neverFails (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftTape : List HashOutput) (rightLength : Nat) :
    Pr[⊥ | padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$>
          (simulateQ (TapeFactor.splitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), ([], []))] = 0 := by
  refine probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨padding_neverFails rightLength,
    fun rightTape _ => ?_⟩
  rw [map_eq_bind_pure_comp]
  exact probFailure_bind_eq_zero_iff _ _ |>.mpr
    ⟨TapeFactor.splitTapeRun_neverFails leftKeep rightKeep computation _, fun _ _ => by simp⟩

open scoped Classical in
/-- **The disclosing block's own law.** An event about it alone is an event about the block
draw, which is what lets the concentration bound be read at the blocked run. -/
theorem prob_leftBlock (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (event : List HashOutput → Prop) :
    Pr[fun outcome : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) =>
        event outcome.1.1 |
      TapeFactor.blockRun leftKeep rightKeep computation cache leftLength rightLength] =
      Pr[event | padding leftLength] := by
  classical
  rw [TapeFactor.blockRun, probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun leftTape => ?_
  have hshape : ∀ outcome ∈ support (padding rightLength >>= fun rightTape =>
        (fun result => ((leftTape, rightTape), result)) <$>
          (simulateQ (TapeFactor.splitTapeRecorder leftKeep rightKeep) computation).run
            (cache, (leftTape, rightTape), ([], []))),
      outcome.1.1 = leftTape := by
    intro outcome hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨rightTape, -, hinner⟩ := hmem
    rw [support_map] at hinner
    obtain ⟨result, -, hbuilt⟩ := hinner
    rw [← hbuilt]
  rw [probEvent_congr' (fun outcome hmem => by rw [hshape outcome hmem]) rfl,
    probEvent_const, blockRun_tail_neverFails leftKeep rightKeep computation cache leftTape
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
theorem prob_targetCovered_le (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (cache : σ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support (recordedRun leftKeep rightKeep computation cache),
      result.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support (recordedRun leftKeep rightKeep computation cache),
      result.2.2.2.length ≤ rightLength) :
    Pr[TargetCovered | recordedRun leftKeep rightKeep computation cache] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        (∑' result, Pr[= result | recordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  set reshape : (List HashOutput × List HashOutput) × (α × TapeFactor.SplitTapeState σ) →
      α × RecorderView.StateOf σ := fun outcome => TapeFactor.forgetSplit outcome.2 with hreshape
  have hlaw := evalDist_recordedRun_eq leftKeep rightKeep computation cache leftLength rightLength
  have hsupport : support (recordedRun leftKeep rightKeep computation cache) =
      support (reshape <$> TapeFactor.blockRun leftKeep rightKeep computation cache leftLength
        rightLength) := Averaging.support_eq_of_evalDist_eq hlaw
  -- The event, moved to the blocked run.
  have hevent : Pr[TargetCovered | recordedRun leftKeep rightKeep computation cache] =
      Pr[fun outcome => TargetCovered (reshape outcome) |
        TapeFactor.blockRun leftKeep rightKeep computation cache leftLength rightLength] := by
    rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_map]
    rfl
  -- The expectation, moved to the blocked run.
  have hexpect : (∑' result, Pr[= result | recordedRun leftKeep rightKeep computation cache] *
        ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
      ∑' outcome, Pr[= outcome |
          TapeFactor.blockRun leftKeep rightKeep computation cache leftLength rightLength] *
        (((TapeFactor.rightOf outcome.2.2).length : Nat) : ℝ≥0∞) := by
    rw [show (∑' result, Pr[= result | recordedRun leftKeep rightKeep computation cache] *
          ((result.2.2.2.length : Nat) : ℝ≥0∞)) =
        ∑' result, Pr[= result | reshape <$> TapeFactor.blockRun leftKeep rightKeep computation
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
      obtain ⟨hleftTape, hrightTape, hrun⟩ := mem_support_blockRun leftKeep rightKeep
        computation cache leftLength rightLength outcome hmem
      have hplain : reshape outcome ∈
          support (recordedRun leftKeep rightKeep computation cache) := by
        rw [hsupport, support_map]
        exact ⟨outcome, hmem, rfl⟩
      obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hentry
      have hrightLen : (TapeFactor.rightOf outcome.2.2).length ≤ rightLength :=
        hrightBound _ hplain
      have hleftLen : (TapeFactor.leftOf outcome.2.2).length ≤ leftLength :=
        hleftBound _ hplain
      have hcellRight := TapeFactor.rightOf_getElem? leftKeep rightKeep computation cache
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
        · have := TapeFactor.leftOf_getElem? leftKeep rightKeep computation cache outcome.1.1
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
      exact TapeFactor.prob_exists_hit_le_expected leftKeep rightKeep computation cache
        leftLength rightLength (GoodBlock leftLength) (BlockHit leftLength) _
        (fun block hgood => prob_blockHit_le leftLength block hgood)

end SlhDsaSecurity.BlockViews

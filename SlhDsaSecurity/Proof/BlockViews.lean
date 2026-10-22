import SlhDsaSecurity.Proof.TapeFactor

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

end SlhDsaSecurity.BlockViews

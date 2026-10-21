import SlhDsaSecurity.Proof.ForsCoverage
import SlhDsaSecurity.Statement.Hashing

/-!
# Coverage after revealing the short hash output

These are fixed-data distribution and counting lemmas. They do not assert that
an adaptive transcript is independent of the remaining digest bits.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.PartialDigest

abbrev Suffix := BitVec 112
abbrev TailTree := Fin 3
abbrev View := MessageDigest.Instance × (TailTree → MessageDigest.ForsLeaf)

def tailTree (tree : TailTree) : MessageDigest.ForsTree :=
  ⟨11 + tree.val, by change _ < 14; omega⟩

def restrict (view : MessageDigest.View) : View :=
  (view.1, fun tree => view.2 (tailTree tree))

def parse (suffix : Suffix) : View :=
  ((suffix.extractLsb' 16 54 ++ suffix.extractLsb' 0 9).toFin,
    fun tree => (suffix.extractLsb' (96 - 12 * tree.val) 12).toFin)

theorem truncate_append (shortOutput : Digest) (suffix : Suffix) :
    Hashing.truncate (shortOutput ++ suffix) = shortOutput := by
  exact BitVec.extractLsb'_append_eq_left

theorem restrict_parse_append (shortOutput : Digest) (suffix : Suffix) :
    restrict (MessageDigest.parse (shortOutput ++ suffix)) = parse suffix := by
  apply Prod.ext
  · simp only [restrict, MessageDigest.parse, MessageDigest.treeIndex,
      MessageDigest.leafIndex, parse, totalHeight, subtreeHeight]
    rw [BitVec.extractLsb'_append_eq_of_add_le (start := 16) (len := 54) (by decide),
      BitVec.extractLsb'_append_eq_of_add_le (start := 0) (len := 9) (by decide)]
  · funext tree
    simp only [restrict, MessageDigest.parse, MessageDigest.forsIndices, parse,
      tailTree, forsHeight, forsTrees]
    have hoff : 72 + 12 * (14 - 1 - (11 + tree.val)) = 96 - 12 * tree.val := by
      have := tree.isLt
      omega
    rw [hoff, BitVec.extractLsb'_append_eq_of_add_le
      (start := 96 - 12 * tree.val) (len := 12) (by omega)]

/-- Keep the nine ordinarily ignored bits and the remaining four bits of index ten. -/
def split (suffix : Suffix) : View × (BitVec 2 × BitVec 7 × BitVec 4) :=
  (parse suffix, suffix.extractLsb' 70 2, suffix.extractLsb' 9 7,
    suffix.extractLsb' 108 4)

theorem split_injective : Function.Injective split := by
  intro left right heq
  have hinstance : left.extractLsb' 16 54 ++ left.extractLsb' 0 9 =
      right.extractLsb' 16 54 ++ right.extractLsb' 0 9 :=
    BitVec.toFin_injective (congrArg (fun x => x.1.1) heq)
  have hleaves := congrArg (fun x => x.1.2) heq
  have hunusedTree := congrArg (fun x => x.2.1) heq
  have hunusedLeaf := congrArg (fun x => x.2.2.1) heq
  have hpartial := congrArg (fun x => x.2.2.2) heq
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  by_cases hleaf : bit < 9
  · have h := congrArg (fun value => value.getLsbD bit) hinstance
    simpa only [BitVec.getLsbD_append, hleaf, ite_true,
      BitVec.getLsbD_extractLsb', hleaf, decide_true, Bool.true_and, Nat.zero_add] using h
  by_cases hleafPad : bit < 16
  · have h := congrArg (fun value => value.getLsbD (bit - 9)) hunusedLeaf
    have hlocal : bit - 9 < 7 := by omega
    have hposition : 9 + (bit - 9) = bit := by omega
    simpa [split, BitVec.getLsbD_extractLsb', hlocal, hposition] using h
  by_cases htree : bit < 70
  · have h := congrArg (fun value => value.getLsbD (bit - 7)) hinstance
    have hnotlow : ¬ bit - 7 < 9 := by omega
    have hlocal : bit - 7 - 9 < 54 := by omega
    have hposition : 16 + (bit - 7 - 9) = bit := by omega
    simpa only [BitVec.getLsbD_append, if_neg hnotlow, BitVec.getLsbD_extractLsb',
      hlocal, decide_true, Bool.true_and, hposition] using h
  by_cases htreePad : bit < 72
  · have h := congrArg (fun value => value.getLsbD (bit - 70)) hunusedTree
    have hlocal : bit - 70 < 2 := by omega
    have hposition : 70 + (bit - 70) = bit := by omega
    simpa [split, BitVec.getLsbD_extractLsb', hlocal, hposition] using h
  by_cases hindices : bit < 108
  · let tree : TailTree := ⟨2 - (bit - 72) / 12, by omega⟩
    have hdigit : left.extractLsb' (96 - 12 * tree.val) 12 =
        right.extractLsb' (96 - 12 * tree.val) 12 :=
      BitVec.toFin_injective (congrFun hleaves tree)
    have h := congrArg (fun value => value.getLsbD ((bit - 72) % 12)) hdigit
    have hlocal : (bit - 72) % 12 < 12 := Nat.mod_lt _ (by decide)
    have hposition : 96 - 12 * tree.val + (bit - 72) % 12 = bit := by
      dsimp [tree]
      omega
    simpa only [BitVec.getLsbD_extractLsb', hlocal, decide_true,
      Bool.true_and, hposition] using h
  · have h := congrArg (fun value => value.getLsbD (bit - 108)) hpartial
    have hlocal : bit - 108 < 4 := by omega
    have hposition : 108 + (bit - 108) = bit := by omega
    simpa [split, BitVec.getLsbD_extractLsb', hlocal, hposition] using h

theorem split_bijective : Function.Bijective split := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨split_injective, ?_⟩
  norm_num [Suffix, View, TailTree, MessageDigest.Instance, MessageDigest.ForsLeaf,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_bitVec,
    totalHeight, forsHeight]

/-- For every fixed short output, the instance and last three indices remain jointly uniform. -/
theorem evalDist_restrict_parse_append_uniform (shortOutput : Digest) :
    𝒟[(fun suffix => restrict (MessageDigest.parse (shortOutput ++ suffix))) <$>
      ($ᵗ Suffix : ProbComp Suffix)] = 𝒟[($ᵗ View : ProbComp View)] := by
  simp_rw [restrict_parse_append]
  have hmap : parse <$> ($ᵗ Suffix : ProbComp Suffix) =
      Prod.fst <$> (split <$> ($ᵗ Suffix : ProbComp Suffix)) := by
    simp [Functor.map_map, split]
  have hsplit := evalDist_map_bijective_uniform_cross (α := Suffix)
    (β := View × (BitVec 2 × BitVec 7 × BitVec 4)) split split_bijective
  rw [hmap, evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

def Covered (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance) (view : View) : Prop :=
  view.1 ∈ instances ∧ ∀ tree, view.2 tree ∈ revealed view.1 (tailTree tree)

instance (revealed : ForsCoverage.Disclosures) (instances : Finset MessageDigest.Instance) :
    DecidablePred (Covered revealed instances) :=
  fun view => inferInstanceAs (Decidable
    (view.1 ∈ instances ∧ ∀ tree, view.2 tree ∈ revealed view.1 (tailTree tree)))

def coveredEquiv (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance) :
    (Σ index : {i // i ∈ instances},
      (tree : TailTree) → {leaf // leaf ∈ revealed index.val (tailTree tree)}) ≃
        {view : View // Covered revealed instances view} where
  toFun choice := ⟨(choice.1.val, fun tree => (choice.2 tree).val),
    choice.1.property, fun tree => (choice.2 tree).property⟩
  invFun view := ⟨⟨view.val.1, view.property.1⟩,
    fun tree => ⟨view.val.2 tree, view.property.2 tree⟩⟩
  left_inv := by rintro ⟨⟨index, hindex⟩, leaves⟩; rfl
  right_inv := by rintro ⟨⟨index, leaves⟩, h⟩; rfl

theorem covered_card_le (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance) (limit : Nat)
    (hcount : ∀ index ∈ instances, ∀ tree, (revealed index tree).card ≤ limit) :
    (Finset.univ.filter (Covered revealed instances)).card ≤ instances.card * limit ^ 3 := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr (coveredEquiv revealed instances),
    Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : {i // i ∈ instances}, limit ^ 3 := by
      apply Finset.sum_le_sum
      intro index _
      rw [Fintype.card_pi]
      calc
        _ ≤ ∏ _ : TailTree, limit := by
          apply Finset.prod_le_prod'
          intro tree _
          simpa using hcount index.val index.property (tailTree tree)
        _ = limit ^ 3 := by simp [TailTree]
    _ = instances.card * limit ^ 3 := by simp

theorem uniform_coverage_le (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance) (limit : Nat)
    (hcount : ∀ index ∈ instances, ∀ tree, (revealed index tree).card ≤ limit) :
    Pr[Covered revealed instances | ($ᵗ View : ProbComp View)] ≤
      ((instances.card * limit ^ 3 : Nat) : ℝ≥0∞) / ((2 ^ 99 : Nat) : ℝ≥0∞) := by
  rw [probEvent_uniformSample]
  have hcard : Fintype.card View = 2 ^ 99 := by
    norm_num [View, TailTree, MessageDigest.Instance, MessageDigest.ForsLeaf,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, totalHeight, forsHeight]
  rw [hcard]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr
    (covered_card_le revealed instances limit hcount)) _

/-- Fixed short output, disclosures, and instance set; no adaptive independence is asserted. -/
theorem coverage_le (shortOutput : Digest) (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance) (limit : Nat)
    (hcount : ∀ index ∈ instances, ∀ tree, (revealed index tree).card ≤ limit) :
    Pr[fun suffix => (MessageDigest.parse (shortOutput ++ suffix)).1 ∈ instances ∧
      ForsCoverage.Covered revealed (MessageDigest.parse (shortOutput ++ suffix)) |
      ($ᵗ Suffix : ProbComp Suffix)] ≤
      ((instances.card * limit ^ 3 : Nat) : ℝ≥0∞) / ((2 ^ 99 : Nat) : ℝ≥0∞) := by
  apply (probEvent_mono (q := fun suffix =>
    Covered revealed instances (restrict (MessageDigest.parse (shortOutput ++ suffix))))
      (fun suffix _ h => ⟨h.1, fun tree => h.2 (tailTree tree)⟩)).trans
  rw [show (fun suffix => Covered revealed instances
      (restrict (MessageDigest.parse (shortOutput ++ suffix)))) =
    Covered revealed instances ∘ (fun suffix => restrict (MessageDigest.parse (shortOutput ++ suffix)))
      from rfl, ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_restrict_parse_append_uniform shortOutput)]
  exact uniform_coverage_le revealed instances limit hcount

theorem coverage_le_256 (shortOutput : Digest) (revealed : ForsCoverage.Disclosures)
    (instances : Finset MessageDigest.Instance)
    (hcount : ∀ index ∈ instances, ∀ tree, (revealed index tree).card ≤ 256) :
    Pr[fun suffix => (MessageDigest.parse (shortOutput ++ suffix)).1 ∈ instances ∧
      ForsCoverage.Covered revealed (MessageDigest.parse (shortOutput ++ suffix)) |
      ($ᵗ Suffix : ProbComp Suffix)] ≤
      (instances.card : ℝ≥0∞) / ((2 ^ 75 : Nat) : ℝ≥0∞) := by
  refine (coverage_le shortOutput revealed instances 256 hcount).trans_eq ?_
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [Nat.cast_mul, Nat.cast_pow, ENNReal.toReal_div, ENNReal.toReal_mul]
  ring

theorem coverage_singleton_le_256 (shortOutput : Digest) (revealed : ForsCoverage.Disclosures)
    (index : MessageDigest.Instance)
    (hcount : ∀ tree, (revealed index tree).card ≤ 256) :
    Pr[fun suffix => (MessageDigest.parse (shortOutput ++ suffix)).1 = index ∧
      ForsCoverage.Covered revealed (MessageDigest.parse (shortOutput ++ suffix)) |
      ($ᵗ Suffix : ProbComp Suffix)] ≤
      1 / ((2 ^ 75 : Nat) : ℝ≥0∞) := by
  simpa only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] using
    coverage_le_256 shortOutput revealed {index}
    (fun candidate hc tree => by
      have heq := Finset.mem_singleton.mp hc
      subst candidate
      exact hcount tree)

end SlhDsaSecurity.PartialDigest

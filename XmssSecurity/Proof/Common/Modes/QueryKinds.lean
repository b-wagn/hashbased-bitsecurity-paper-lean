import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Common.EUFCMA.Modes

/-!
# Counting modes as sets of query kinds

The statement layer has one experiment per notion, returning a count per `QueryKind`, and a counting
mode is a set `Z` of kinds whose counts are summed (`SecurityGame`). This file works with the
variant `lossyGame` of the statement's game in which a repeated epoch loses (`LossyGames.lean`). The
proofs use the per-mode formulation of `Proof/Legacy/PerModeNotions.lean`: one notion per
`CountingMode`, whose experiment returns the single charged number. This file proves the two
formulations equivalent for every set `Z` containing the adversary's own hash queries: the
experiment of `lossyGame` is `gameDetailed` (by definition), and summing the kinds in `Z` is the
weight of the mode `modeOf Z`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Modes

open SUFCMA

/-- The per-mode counting mode charging the kinds in `Z`, besides the adversary's own hash
queries, which every per-mode notion charges. -/
def modeOf (Z : Finset QueryKind) : CountingMode :=
  ⟨decide (QueryKind.keygen ∈ Z), decide (QueryKind.signer ∈ Z), decide (QueryKind.verifier ∈ Z),
    decide (QueryKind.sign ∈ Z)⟩

/-- Summing the counts of the kinds in `Z` is the weight of `modeOf Z`, if `Z` contains `hash`. -/
lemma sum_eq_weight (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z) (c : QueryCounts) :
    ∑ kind ∈ Z, c kind = (modeOf Z).weight c := by
  have huniv : (Finset.univ : Finset QueryKind) =
      {.sign, .hash, .keygen, .signer, .verifier} := by decide
  rw [← Finset.univ_inter Z, ← Finset.sum_ite_mem, huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
    not_false_eq_true, Finset.sum_singleton, CountingMode.weight_apply, modeOf, hZ, if_true]
  by_cases h1 : QueryKind.sign ∈ Z <;> by_cases h2 : QueryKind.keygen ∈ Z <;>
    by_cases h3 : QueryKind.signer ∈ Z <;> by_cases h4 : QueryKind.verifier ∈ Z <;>
    simp [h1, h2, h3, h4] <;> ring

section strong

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output] [DecidableEq Msg] [DecidableEq Sig]

/-- The per-mode experiment of `modeOf Z` is the statement's experiment with the counts of the
kinds in `Z` summed. -/
lemma notion_experiment_eq (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion (modeOf Z)).experiment scheme adversary =
      (fun r => (r.1, ∑ kind ∈ Z, r.2 kind)) <$>
        (SUFCMA.lossyGame (PK := PK) (SK := SK)).experiment scheme adversary := by
  rw [experiment_notion_eq]
  simp only [sum_eq_weight Z hZ]
  rfl

/-- Bit security of the statement's game in mode `Z` is bit security of the per-mode notion. -/
theorem hasClassicalSecurityBound_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (workFactor : ℝ≥0∞) :
    (SUFCMA.lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBound scheme Z workFactor ↔
      (notion (modeOf Z)).HasClassicalSecurityBound scheme workFactor := by
  have hadv : ∀ adversary,
      (SUFCMA.lossyGame (PK := PK) (SK := SK)).advantage scheme adversary =
        (notion (modeOf Z)).advantage scheme adversary := by
    intro adversary
    simp only [SecurityGame.advantage, SecurityNotion.advantage,
      notion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound : ∀ adversary q,
      (SUFCMA.lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q ↔
        (notion (modeOf Z)).HasQueryBound scheme adversary q := by
    intro adversary q
    simp only [SecurityGame.HasQueryBound, SecurityNotion.HasQueryBound,
      notion_experiment_eq Z hZ scheme adversary, probEvent_eq_one_iff, probFailure_eq_zero,
      true_and, support_map, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  constructor
  · intro h q hq adversary hb
    rw [← hadv]
    exact h q hq adversary ((hbound adversary q).2 hb)
  · intro h q hq adversary hb
    rw [hadv]
    exact h q hq adversary ((hbound adversary q).1 hb)


theorem hasClassicalSecurityBits_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) :
    (SUFCMA.lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits ↔
      (notion (modeOf Z)).HasClassicalSecurityBits scheme bits := by
  have hadv : ∀ adversary,
      (SUFCMA.lossyGame (PK := PK) (SK := SK)).advantage scheme adversary =
        (notion (modeOf Z)).advantage scheme adversary := by
    intro adversary
    simp only [SecurityGame.advantage, SecurityNotion.advantage,
      notion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound : ∀ adversary q,
      (SUFCMA.lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q ↔
        (notion (modeOf Z)).HasQueryBound scheme adversary q := by
    intro adversary q
    simp only [SecurityGame.HasQueryBound, SecurityNotion.HasQueryBound,
      notion_experiment_eq Z hZ scheme adversary, probEvent_eq_one_iff, probFailure_eq_zero,
      true_and, support_map, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  constructor
  · intro h q hq adversary hb
    rw [← hadv]
    exact h q hq adversary ((hbound adversary q).2 hb)
  · intro h q hq adversary hb
    rw [hadv]
    exact h q hq adversary ((hbound adversary q).1 hb)

/-- Exact bit security of the statement's game in mode `Z` is exact bit security of the
per-mode notion. -/
theorem hasExactClassicalSecurityBits_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) :
    (SUFCMA.lossyGame (PK := PK) (SK := SK)).HasExactClassicalSecurityBits scheme Z bits ↔
      (notion (modeOf Z)).HasExactClassicalSecurityBits scheme bits := by
  simp only [SecurityGame.HasExactClassicalSecurityBits,
    SecurityNotion.HasExactClassicalSecurityBits, hasClassicalSecurityBits_iff Z hZ]

end strong

section standard

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output] [DecidableEq Msg]

/-- The per-mode EUF-CMA experiment of `modeOf Z` is the statement's experiment with the counts
of the kinds in `Z` summed. -/
lemma eufNotion_experiment_eq (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (EUFCMA.notion (modeOf Z)).experiment scheme adversary =
      (fun r => (r.1, ∑ kind ∈ Z, r.2 kind)) <$>
        (EUFCMA.lossyGame (PK := PK) (SK := SK)).experiment scheme adversary := by
  rw [EUFCMA.experiment_notion_eq]
  simp only [sum_eq_weight Z hZ]
  rfl

/-- Bit security of the statement's EUF-CMA game in mode `Z` is bit security of the per-mode
notion. -/
theorem eufHasClassicalSecurityBound_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (workFactor : ℝ≥0∞) :
    (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBound scheme Z workFactor ↔
      (EUFCMA.notion (modeOf Z)).HasClassicalSecurityBound scheme workFactor := by
  have hadv : ∀ adversary,
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).advantage scheme adversary =
        (EUFCMA.notion (modeOf Z)).advantage scheme adversary := by
    intro adversary
    simp only [SecurityGame.advantage, SecurityNotion.advantage,
      eufNotion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound : ∀ adversary q,
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q ↔
        (EUFCMA.notion (modeOf Z)).HasQueryBound scheme adversary q := by
    intro adversary q
    simp only [SecurityGame.HasQueryBound, SecurityNotion.HasQueryBound,
      eufNotion_experiment_eq Z hZ scheme adversary, probEvent_eq_one_iff, probFailure_eq_zero,
      true_and, support_map, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  constructor
  · intro h q hq adversary hb
    rw [← hadv]
    exact h q hq adversary ((hbound adversary q).2 hb)
  · intro h q hq adversary hb
    rw [hadv]
    exact h q hq adversary ((hbound adversary q).1 hb)


theorem eufHasClassicalSecurityBits_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) :
    (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasClassicalSecurityBits scheme Z bits ↔
      (EUFCMA.notion (modeOf Z)).HasClassicalSecurityBits scheme bits := by
  have hadv : ∀ adversary,
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).advantage scheme adversary =
        (EUFCMA.notion (modeOf Z)).advantage scheme adversary := by
    intro adversary
    simp only [SecurityGame.advantage, SecurityNotion.advantage,
      eufNotion_experiment_eq Z hZ scheme adversary, probEvent_map]
    rfl
  have hbound : ∀ adversary q,
      (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasQueryBound scheme Z adversary q ↔
        (EUFCMA.notion (modeOf Z)).HasQueryBound scheme adversary q := by
    intro adversary q
    simp only [SecurityGame.HasQueryBound, SecurityNotion.HasQueryBound,
      eufNotion_experiment_eq Z hZ scheme adversary, probEvent_eq_one_iff, probFailure_eq_zero,
      true_and, support_map, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
  constructor
  · intro h q hq adversary hb
    rw [← hadv]
    exact h q hq adversary ((hbound adversary q).2 hb)
  · intro h q hq adversary hb
    rw [hadv]
    exact h q hq adversary ((hbound adversary q).1 hb)

/-- Exact bit security of the statement's EUF-CMA game in mode `Z` is exact bit security of the
per-mode notion. -/
theorem eufHasExactClassicalSecurityBits_iff (Z : Finset QueryKind) (hZ : QueryKind.hash ∈ Z)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) :
    (EUFCMA.lossyGame (PK := PK) (SK := SK)).HasExactClassicalSecurityBits scheme Z bits ↔
      (EUFCMA.notion (modeOf Z)).HasExactClassicalSecurityBits scheme bits := by
  simp only [SecurityGame.HasExactClassicalSecurityBits,
    SecurityNotion.HasExactClassicalSecurityBits, eufHasClassicalSecurityBits_iff Z hZ]

end standard

end XmssSecurity.Modes

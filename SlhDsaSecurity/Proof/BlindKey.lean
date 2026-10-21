import VCVio.OracleComp.Constructions.SampleableType
import Mathlib.Data.BitVec

/-!
# Blind-key counting in one independent transcript experiment

A transcript is sampled without the hidden key table. Its guesses may depend on
all its public answers and may be allocated adaptively among key roles. The
expected charge is measured in this same transcript distribution. Applying this
lemma to a real game requires a coupling that preserves replies up to the first
key hit, and an explicit total-budget cap on the blind execution.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BlindKey

abbrev Key := BitVec 128
abbrev Guesses (Index : Type) := List (Index × Key)

variable {Index : Type} [Fintype Index] [DecidableEq Index]

/-- Every coordinate of an independently sampled key table is uniform. -/
theorem coordinate_probability (index : Index) (guess : Key) :
    Pr[fun table : Index → Key => table index = guess |
      ($ᵗ (Index → Key) : ProbComp (Index → Key))] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hdist := evalDist_uniformSample_bind_update (R := Key) index
  calc
    _ = Pr[fun table : Index → Key => table index = guess |
        (do let value ← $ᵗ Key
            let table ← $ᵗ (Index → Key)
            pure (Function.update table index value))] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) hdist).symm
    _ = Pr[= guess | ($ᵗ Key : ProbComp Key)] := by
      rw [probEvent_bind_eq_tsum]
      simp only [bind_pure_comp, probEvent_map, Function.comp_def, Function.update_self]
      rw [← probEvent_eq_eq_probOutput, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro value
      by_cases heq : value = guess <;> simp [heq]
    _ = _ := by simp [probOutput_uniformSample, Key]

def Hit (guesses : Guesses Index) (table : Index → Key) : Prop :=
  ∃ guess ∈ guesses, table guess.1 = guess.2

/-- Repeated guesses can be charged again; one entry tests only one key role. -/
theorem hit_probability_le (guesses : Guesses Index) :
    Pr[Hit guesses | ($ᵗ (Index → Key) : ProbComp (Index → Key))] ≤
      guesses.length / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  induction guesses with
  | nil => simp [Hit]
  | cons guess rest ih =>
      have hevent : Hit (guess :: rest) =
          fun table => table guess.1 = guess.2 ∨ Hit rest table := by
        funext table
        simp [Hit]
      rw [hevent]
      calc
        _ ≤ Pr[fun table : Index → Key => table guess.1 = guess.2 |
            ($ᵗ (Index → Key) : ProbComp (Index → Key))] +
          Pr[Hit rest | ($ᵗ (Index → Key) : ProbComp (Index → Key))] :=
          probEvent_or_le _ _ _
        _ ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            rest.length / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
          add_le_add (le_of_eq (coordinate_probability guess.1 guess.2)) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

/-- The expected number of guesses in the blind transcript distribution. -/
noncomputable def expectedGuesses {Transcript : Type}
    (transcripts : ProbComp Transcript) (guesses : Transcript → Guesses Index) : ℝ≥0∞ :=
  ∑' transcript, Pr[= transcript | transcripts] * (guesses transcript).length

/-- Multiple secret-key roles are counted together in one key-independent experiment.
No claim about the real transcript distribution is implicit in this statement. -/
theorem mixture_hit_le_expected {Transcript : Type}
    (transcripts : ProbComp Transcript) (guesses : Transcript → Guesses Index) :
    Pr[fun result : Transcript × (Index → Key) => Hit (guesses result.1) result.2 |
      (do let transcript ← transcripts
          let table ← $ᵗ (Index → Key)
          pure (transcript, table))] ≤
      expectedGuesses transcripts guesses / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  calc
    _ ≤ ∑' transcript, Pr[= transcript | transcripts] *
        ((guesses transcript).length / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro transcript
      exact mul_le_mul' le_rfl (hit_probability_le (guesses transcript))
    _ = _ := by
      simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      rfl

omit [Fintype Index] [DecidableEq Index] in
/-- A support-wise total cap must hold in the blind game itself. It then bounds the
expected key-guess charge, including transcripts outside the real game's support. -/
theorem expectedGuesses_le_of_cap {Transcript : Type}
    (transcripts : ProbComp Transcript) (guesses : Transcript → Guesses Index) (q : Nat)
    (hcap : ∀ transcript ∈ support transcripts, (guesses transcript).length ≤ q) :
    expectedGuesses transcripts guesses ≤ q := by
  unfold expectedGuesses
  calc
    _ ≤ ∑' transcript, Pr[= transcript | transcripts] * q := by
      apply ENNReal.tsum_le_tsum
      intro transcript
      by_cases hmem : transcript ∈ support transcripts
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hcap transcript hmem))
      · have hzero : Pr[= transcript | transcripts] = 0 := by
          exact probOutput_eq_zero_of_not_mem_support hmem
        rw [hzero, zero_mul, zero_mul]
    _ = (∑' transcript, Pr[= transcript | transcripts]) * q := ENNReal.tsum_mul_right
    _ ≤ 1 * q := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = q := one_mul _

omit [Fintype Index] [DecidableEq Index] in
/-- Key guesses and other charges share one transcript and one pathwise cap. This
is the accounting form needed when the adversary adaptively allocates query roles. -/
theorem expectedGuesses_add_cost_le {Transcript : Type}
    (transcripts : ProbComp Transcript) (guesses : Transcript → Guesses Index)
    (other : Transcript → Nat) (q : Nat)
    (hcap : ∀ transcript ∈ support transcripts,
      (guesses transcript).length + other transcript ≤ q) :
    expectedGuesses transcripts guesses +
      (∑' transcript, Pr[= transcript | transcripts] * other transcript) ≤ q := by
  unfold expectedGuesses
  rw [← ENNReal.tsum_add]
  calc
    _ = ∑' transcript, Pr[= transcript | transcripts] *
        ((guesses transcript).length + other transcript : Nat) := by
      apply tsum_congr
      intro transcript
      simp only [Nat.cast_add, mul_add]
    _ ≤ ∑' transcript, Pr[= transcript | transcripts] * q := by
      apply ENNReal.tsum_le_tsum
      intro transcript
      by_cases hmem : transcript ∈ support transcripts
      · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hcap transcript hmem))
      · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = (∑' transcript, Pr[= transcript | transcripts]) * q := ENNReal.tsum_mul_right
    _ ≤ 1 * q := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = q := one_mul _

end SlhDsaSecurity.BlindKey

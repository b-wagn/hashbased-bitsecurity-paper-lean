import SlhDsaSecurity.Proof.ForsCoverage

/-!
# Adaptive selection from an independent target tape

The policy decides whether to use target j from the preceding target values.
Disclosures are fixed and may include an entire padded honest-signing tape,
including its future disclosures. This file proves an expected-count bound for
this finite experiment, not a simulation theorem for the concrete shared ROM.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ForsAdaptiveTargets

abbrev View := ForsCoverage.View
abbrev Tape (trials : Nat) := Fin trials → View
abbrev Policy (trials : Nat) := (j : Fin trials) → (Fin j.val → View) → Bool

def history {trials : Nat} (tape : Tape trials) (j : Fin trials) : Fin j.val → View :=
  fun i => tape ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩

theorem history_update {trials : Nat} (tape : Tape trials) (j : Fin trials) (value : View) :
    history (Function.update tape j value) j = history tape j := by
  funext i
  have hne : (⟨i.val, Nat.lt_trans i.isLt j.isLt⟩ : Fin trials) ≠ j := by
    intro h
    exact (Nat.ne_of_lt i.isLt) (congrArg Fin.val h)
  simp [history, Function.update_of_ne hne]

/-- Resampling the current coordinate preserves any decision made from its preceding history. -/
theorem selected_hit_factor {trials : Nat} (policy : Policy trials) (j : Fin trials)
    (hit : View → Prop) [DecidablePred hit] :
    Pr[fun tape => policy j (history tape j) = true ∧ hit (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] =
      Pr[fun tape => policy j (history tape j) = true | ($ᵗ Tape trials : ProbComp (Tape trials))] *
        Pr[hit | ($ᵗ View : ProbComp View)] := by
  let selected : Tape trials → Prop := fun tape => policy j (history tape j) = true
  have hdist := evalDist_uniformSample_bind_update (R := View) j
  have hinner (value : View) :
      Pr[fun tape => selected (Function.update tape j value) ∧
          hit ((Function.update tape j value) j) | ($ᵗ Tape trials : ProbComp (Tape trials))] =
      if hit value then Pr[selected | ($ᵗ Tape trials : ProbComp (Tape trials))] else 0 := by
    by_cases hv : hit value <;> simp [selected, history_update, hv]
  calc
    _ = Pr[fun tape => selected tape ∧ hit (tape j) |
        (do let value ← $ᵗ View
            let tape ← $ᵗ Tape trials
            pure (Function.update tape j value))] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) hdist).symm
    _ = ∑' value : View, Pr[= value | ($ᵗ View : ProbComp View)] *
        (if hit value then Pr[selected | ($ᵗ Tape trials : ProbComp (Tape trials))] else 0) := by
      rw [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro value
      rw [bind_pure_comp, probEvent_map]
      exact congrArg _ (hinner value)
    _ = (∑' value : View, if hit value then Pr[= value | ($ᵗ View : ProbComp View)] else 0) *
        Pr[selected | ($ᵗ Tape trials : ProbComp (Tape trials))] := by
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro value
      split_ifs <;> simp
    _ = _ := by rw [← probEvent_eq_tsum_ite, mul_comm]

def uses {trials : Nat} (policy : Policy trials) (tape : Tape trials) : Nat :=
  (Finset.univ.filter (fun j => policy j (history tape j) = true)).card

/-- The actual expected number of selected coordinates, with no deterministic role cap. -/
noncomputable def expectedUses {trials : Nat} (policy : Policy trials) : ℝ≥0∞ :=
  ∑ tape : Tape trials, Pr[= tape | ($ᵗ Tape trials : ProbComp (Tape trials))] * uses policy tape

theorem expectedUses_eq_sum_prob {trials : Nat} (policy : Policy trials) :
    expectedUses policy = ∑ j : Fin trials,
      Pr[fun tape => policy j (history tape j) = true |
        ($ᵗ Tape trials : ProbComp (Tape trials))] := by
  classical
  unfold expectedUses uses
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [probEvent_eq_sum_fintype_ite]
  apply Finset.sum_congr rfl
  intro tape _
  split_ifs <;> simp

/-- A union bound charged to the random adaptive number of selected target coordinates. -/
theorem selected_hit_le_expected {trials : Nat} (policy : Policy trials)
    (hit : View → Prop) [DecidablePred hit] (rate : ℝ≥0∞)
    (hrate : Pr[hit | ($ᵗ View : ProbComp View)] ≤ rate) :
    Pr[fun tape => ∃ j, policy j (history tape j) = true ∧ hit (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤ expectedUses policy * rate := by
  have hevent : (fun tape => ∃ j, policy j (history tape j) = true ∧ hit (tape j)) =
      (fun tape => ∃ j ∈ (Finset.univ : Finset (Fin trials)),
        policy j (history tape j) = true ∧ hit (tape j)) := by
    funext tape
    simp
  rw [hevent]
  calc
    _ ≤ ∑ j : Fin trials,
      Pr[fun tape => policy j (history tape j) = true ∧ hit (tape j) |
        ($ᵗ Tape trials : ProbComp (Tape trials))] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ j : Fin trials,
      Pr[fun tape => policy j (history tape j) = true |
        ($ᵗ Tape trials : ProbComp (Tape trials))] * rate := by
      apply Finset.sum_le_sum
      intro j _
      rw [selected_hit_factor]
      exact mul_le_mul' le_rfl hrate
    _ = _ := by rw [← Finset.sum_mul, ← expectedUses_eq_sum_prob]

/-- Fixed full disclosures can include future honest disclosures. Their load cap gives
the rate for every adaptively selected fresh target; the policy may depend on those fixed data. -/
theorem coverage_le_expected {trials : Nat} (policy : Policy trials)
    (revealed : ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 103) :
    Pr[fun tape => ∃ j, policy j (history tape j) = true ∧
      ForsCoverage.Covered revealed (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      expectedUses policy / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    selected_hit_le_expected policy (ForsCoverage.Covered revealed)
      (1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
      (ForsCoverage.fresh_coverage_le_of_loads revealed loads hload hmoment)

/-- Auxiliary data are sampled before an independent target tape. They may contain the
entire honest tape and private coins. The policy may depend arbitrarily on these data.
Only the failure probability of their load cap is added to the expected query charge. -/
theorem coverage_mixture_le {Aux : Type} {trials : Nat} (data : ProbComp Aux)
    (policies : Aux → Policy trials) (revealed : Aux → ForsCoverage.Disclosures)
    (loads : Aux → ForsCoverage.Instance → Nat) (good : Aux → Prop)
    (hload : ∀ auxiliary, good auxiliary → ∀ index tree,
      (revealed auxiliary index tree).card ≤ loads auxiliary index)
    (hmoment : ∀ auxiliary, good auxiliary →
      ∑ index, loads auxiliary index ^ 14 ≤ 2 ^ 103) :
    Pr[fun result : Aux × Tape trials => ∃ j,
      policies result.1 j (history result.2 j) = true ∧
        ForsCoverage.Covered (revealed result.1) (result.2 j) |
      (do let auxiliary ← data
          let tape ← $ᵗ Tape trials
          pure (auxiliary, tape))] ≤
      Pr[fun auxiliary => ¬good auxiliary | data] +
        (∑' auxiliary, Pr[= auxiliary | data] * expectedUses (policies auxiliary)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  let event (auxiliary : Aux) (tape : Tape trials) : Prop := ∃ j,
    policies auxiliary j (history tape j) = true ∧
      ForsCoverage.Covered (revealed auxiliary) (tape j)
  have hpointwise (auxiliary : Aux) :
      Pr[event auxiliary | ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
        (if good auxiliary then 0 else 1) +
          expectedUses (policies auxiliary) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    by_cases hg : good auxiliary
    · rw [if_pos hg, zero_add]
      exact coverage_le_expected (policies auxiliary) (revealed auxiliary) (loads auxiliary)
        (hload auxiliary hg) (hmoment auxiliary hg)
    · rw [if_neg hg]
      exact le_add_right probEvent_le_one
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  change (∑' auxiliary, Pr[= auxiliary | data] *
    Pr[event auxiliary | ($ᵗ Tape trials : ProbComp (Tape trials))]) ≤ _
  calc
    _ ≤ ∑' auxiliary, Pr[= auxiliary | data] *
        ((if good auxiliary then 0 else 1) +
          expectedUses (policies auxiliary) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro auxiliary
      exact mul_le_mul' le_rfl (hpointwise auxiliary)
    _ = (∑' auxiliary, Pr[= auxiliary | data] * (if good auxiliary then 0 else 1)) +
        (∑' auxiliary, Pr[= auxiliary | data] * expectedUses (policies auxiliary)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ = _ := by
      congr 1
      rw [probEvent_eq_tsum_ite]
      apply tsum_congr
      intro auxiliary
      by_cases hg : good auxiliary <;> simp [hg]

end SlhDsaSecurity.ForsAdaptiveTargets

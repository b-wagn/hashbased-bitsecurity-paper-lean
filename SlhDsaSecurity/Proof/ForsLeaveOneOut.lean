import SlhDsaSecurity.Proof.ForsAdaptiveTargets
import SlhDsaSecurity.Proof.ForsDisclosureTape
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Adaptive FORS targets with their own disclosure removed

All fresh message digests may share one independent tape, including direct
queries and later signing choices. For candidate coordinate j, disclosures and
their local load condition must ignore j. A single good condition on the full
tape implies every local condition; its failure is charged only once.

This is a finite probabilistic theorem. The actual shared-ROM simulation and the
argument that a novel accepted signature's input was never signed are separate.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ForsLeaveOneOut

open ForsAdaptiveTargets

/-- Resampling the current target while fixing every other tape coordinate
preserves any decision based on earlier targets. -/
theorem selected_local_hit_le {trials : Nat} (policy : Policy trials) (j : Fin trials)
    (revealed : Tape trials → ForsCoverage.Disclosures)
    (localGood : Tape trials → Prop) (rate : ℝ≥0∞)
    (hrevealed : ∀ tape value, revealed (Function.update tape j value) = revealed tape)
    (hlocal : ∀ tape value, localGood (Function.update tape j value) ↔ localGood tape)
    (hrate : ∀ tape, localGood tape →
      Pr[ForsCoverage.Covered (revealed tape) | ($ᵗ View : ProbComp View)] ≤ rate) :
    Pr[fun tape => policy j (history tape j) = true ∧ localGood tape ∧
      ForsCoverage.Covered (revealed tape) (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      Pr[fun tape => policy j (history tape j) = true |
        ($ᵗ Tape trials : ProbComp (Tape trials))] * rate := by
  classical
  let event (tape : Tape trials) : Prop := policy j (history tape j) = true ∧
    localGood tape ∧ ForsCoverage.Covered (revealed tape) (tape j)
  have hdist :
      𝒟[(do let tape ← $ᵗ Tape trials
             let value ← $ᵗ View
             pure (Function.update tape j value))] =
        𝒟[($ᵗ Tape trials : ProbComp (Tape trials))] := by
    exact (OracleComp.DeferredSampling.evalDist_bind_comm
      ($ᵗ Tape trials) ($ᵗ View) (fun tape value => pure (Function.update tape j value))).trans
      (evalDist_uniformSample_bind_update (R := View) j)
  have hinner (tape : Tape trials) :
      Pr[fun value => event (Function.update tape j value) | ($ᵗ View : ProbComp View)] ≤
        (if policy j (history tape j) = true then 1 else 0) * rate := by
    have hevent : (fun value => event (Function.update tape j value)) =
        (fun value => policy j (history tape j) = true ∧ localGood tape ∧
          ForsCoverage.Covered (revealed tape) value) := by
      funext value
      simp only [event, history_update, hlocal, hrevealed, Function.update_self]
    rw [hevent]
    by_cases hchosen : policy j (history tape j) = true
    · rw [if_pos hchosen, one_mul]
      by_cases hg : localGood tape
      · simpa only [hchosen, hg, true_and] using hrate tape hg
      · simp only [hg, false_and, and_false, probEvent_False, zero_le]
    · rw [if_neg hchosen, zero_mul]
      apply le_of_eq
      apply probEvent_eq_zero
      intro value _ hhit
      exact hchosen hhit.1
  calc
    _ = Pr[event |
        (do let tape ← $ᵗ Tape trials
            let value ← $ᵗ View
            pure (Function.update tape j value))] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) hdist).symm
    _ ≤ ∑' tape : Tape trials, Pr[= tape | ($ᵗ Tape trials : ProbComp (Tape trials))] *
        ((if policy j (history tape j) = true then 1 else 0) * rate) := by
      rw [probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro tape
      rw [bind_pure_comp, probEvent_map]
      exact mul_le_mul' le_rfl (hinner tape)
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro tape
      split_ifs <;> simp

/-- The global bad-load event is paid once, while every selected fresh coordinate
is charged using only the disclosures from the other coordinates. -/
theorem coverage_le {trials : Nat} (policy : Policy trials)
    (revealed : Fin trials → Tape trials → ForsCoverage.Disclosures)
    (localGood : Fin trials → Tape trials → Prop) (good : Tape trials → Prop)
    (rate : ℝ≥0∞)
    (hrevealed : ∀ j tape value,
      revealed j (Function.update tape j value) = revealed j tape)
    (hlocal : ∀ j tape value,
      localGood j (Function.update tape j value) ↔ localGood j tape)
    (hgood : ∀ tape, good tape → ∀ j, localGood j tape)
    (hrate : ∀ j tape, localGood j tape →
      Pr[ForsCoverage.Covered (revealed j tape) | ($ᵗ View : ProbComp View)] ≤ rate) :
    Pr[fun tape => ∃ j, policy j (history tape j) = true ∧
      ForsCoverage.Covered (revealed j tape) (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      Pr[fun tape => ¬good tape | ($ᵗ Tape trials : ProbComp (Tape trials))] +
        expectedUses policy * rate := by
  classical
  have hevent :
      Pr[fun tape => ∃ j, policy j (history tape j) = true ∧
        ForsCoverage.Covered (revealed j tape) (tape j) |
        ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      Pr[fun tape => ¬good tape ∨ ∃ j ∈ (Finset.univ : Finset (Fin trials)),
        policy j (history tape j) = true ∧ localGood j tape ∧
          ForsCoverage.Covered (revealed j tape) (tape j) |
        ($ᵗ Tape trials : ProbComp (Tape trials))] := by
    apply probEvent_mono
    intro tape _ hhit
    by_cases hg : good tape
    · obtain ⟨j, hchosen, hcovered⟩ := hhit
      exact Or.inr ⟨j, Finset.mem_univ j, hchosen, hgood tape hg j, hcovered⟩
    · exact Or.inl hg
  apply hevent.trans
  calc
    _ ≤ Pr[fun tape => ¬good tape | ($ᵗ Tape trials : ProbComp (Tape trials))] +
        Pr[fun tape => ∃ j ∈ (Finset.univ : Finset (Fin trials)),
          policy j (history tape j) = true ∧ localGood j tape ∧
            ForsCoverage.Covered (revealed j tape) (tape j) |
          ($ᵗ Tape trials : ProbComp (Tape trials))] := probEvent_or_le _ _ _
    _ ≤ Pr[fun tape => ¬good tape | ($ᵗ Tape trials : ProbComp (Tape trials))] +
        ∑ j : Fin trials, Pr[fun tape => policy j (history tape j) = true ∧
          localGood j tape ∧ ForsCoverage.Covered (revealed j tape) (tape j) |
          ($ᵗ Tape trials : ProbComp (Tape trials))] := by
      exact add_le_add le_rfl (probEvent_exists_finset_le_sum _ _ _)
    _ ≤ Pr[fun tape => ¬good tape | ($ᵗ Tape trials : ProbComp (Tape trials))] +
        ∑ j : Fin trials, Pr[fun tape => policy j (history tape j) = true |
          ($ᵗ Tape trials : ProbComp (Tape trials))] * rate := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j _
      exact selected_local_hit_le policy j (revealed j) (localGood j) rate
        (hrevealed j) (hlocal j) (hrate j)
    _ = _ := by rw [← Finset.sum_mul, ← expectedUses_eq_sum_prob]

/-- A full-tape cap suffices: the local condition is that some replacement at j
satisfies the full cap. This condition ignores j, without adding a dummy disclosure. -/
theorem coverage_le_of_full_cap {trials : Nat} (policy : Policy trials)
    (revealed : Fin trials → Tape trials → ForsCoverage.Disclosures)
    (good : Tape trials → Prop) (rate : ℝ≥0∞)
    (hrevealed : ∀ j tape value,
      revealed j (Function.update tape j value) = revealed j tape)
    (hrate : ∀ tape, good tape → ∀ j,
      Pr[ForsCoverage.Covered (revealed j tape) | ($ᵗ View : ProbComp View)] ≤ rate) :
    Pr[fun tape => ∃ j, policy j (history tape j) = true ∧
      ForsCoverage.Covered (revealed j tape) (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      Pr[fun tape => ¬good tape | ($ᵗ Tape trials : ProbComp (Tape trials))] +
        expectedUses policy * rate := by
  let localGood (j : Fin trials) (tape : Tape trials) : Prop :=
    ∃ value, good (Function.update tape j value)
  apply coverage_le policy revealed localGood good rate hrevealed
  · intro j tape value
    simp only [localGood, Function.update_idem]
  · intro tape hgood j
    exact ⟨tape j, by simpa only [Function.update_eq_self] using hgood⟩
  · intro j tape hlocal
    obtain ⟨value, hgood⟩ := hlocal
    simpa only [hrevealed] using hrate (Function.update tape j value) hgood j

/-- Actual fourteen-tree disclosures from all other tape coordinates. Arbitrary
causal selection of the target coordinates is charged by its expected count. -/
theorem independent_tape_coverage_le (trials : Nat) (htrials : trials ≤ 5 * 2 ^ 62)
    (policy : Policy trials) :
    Pr[fun tape => ∃ j, policy j (history tape j) = true ∧
      ForsCoverage.Covered (ForsDisclosureTape.disclosuresExcept j tape) (tape j) |
      ($ᵗ Tape trials : ProbComp (Tape trials))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 + expectedUses policy / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmain := coverage_le_of_full_cap policy ForsDisclosureTape.disclosuresExcept
    (fun tape => ∑ i, ForsDisclosureTape.loads tape i ^ 14 ≤ 2 ^ 103)
    (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) ForsDisclosureTape.disclosuresExcept_update_self
    (fun tape hgood j => ForsCoverage.fresh_coverage_le_of_loads
      (ForsDisclosureTape.disclosuresExcept j tape) (ForsDisclosureTape.loads tape)
      (ForsDisclosureTape.disclosuresExcept_card_le_loads j tape) hgood)
  have hbad := ForsDisclosureTape.bad_load_probability trials htrials
  simp only [not_le] at hmain
  exact hmain.trans (add_le_add hbad (by simp only [div_eq_mul_inv, one_mul]; exact le_rfl))

/-- Independent auxiliary randomness may determine the policy. In particular it
may contain private coins and the unused bits of every full hash answer. -/
theorem independent_tape_mixture_coverage_le {Aux : Type}
    (data : ProbComp Aux) (trials : Nat) (htrials : trials ≤ 5 * 2 ^ 62)
    (policies : Aux → Policy trials) :
    Pr[fun result : Aux × Tape trials => ∃ j,
      policies result.1 j (history result.2 j) = true ∧
        ForsCoverage.Covered (ForsDisclosureTape.disclosuresExcept j result.2) (result.2 j) |
      (do let auxiliary ← data
          let tape ← $ᵗ Tape trials
          pure (auxiliary, tape))] ≤
      (1 : ℝ≥0∞) / 2 ^ 141 +
        (∑' auxiliary, Pr[= auxiliary | data] * expectedUses (policies auxiliary)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  calc
    _ ≤ ∑' auxiliary, Pr[= auxiliary | data] *
        ((1 : ℝ≥0∞) / 2 ^ 141 +
          expectedUses (policies auxiliary) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
      apply ENNReal.tsum_le_tsum
      intro auxiliary
      exact mul_le_mul' le_rfl
        (independent_tape_coverage_le trials htrials (policies auxiliary))
    _ = (∑' auxiliary, Pr[= auxiliary | data]) * ((1 : ℝ≥0∞) / 2 ^ 141) +
        (∑' auxiliary, Pr[= auxiliary | data] * expectedUses (policies auxiliary)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add]
      simp only [ENNReal.tsum_mul_right]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)


/-! ## The statement's signing limit fits the tape bound

`independent_tape_coverage_le_sharper` needs at most `5 * 2 ^ 62` trials, and `signingLimit`
is `2 ^ 64 = 4 * 2 ^ 62`, four fifths of it. That arithmetic is right and is what
`signingLimit_le_tapeBound` proves.

**The item is not a signing request, and an earlier version of this paragraph said it was.**
In `independent_tape_coverage_le_sharper` every tape coordinate plays both roles — coordinate
`j` is a candidate target and every other coordinate discloses (`disclosuresExcept j`) — so
`trials` ranges over targets together with disclosers, which is what this file's own header and
`BlockDisclosures` both say, and the latter builds its index split precisely to escape the
resulting `5 * 2 ^ 62` ceiling.

The live use of `signingLimit_le_tapeBound` is a different one and is sound: it discharges
`BlockViews.prob_targetCovered_le`'s `hcap`, which bounds only the **disclosing** recording,
where the item really is one served request (`ServedAgreement.record_length_le_cap`); the target
count is free there and charged in expectation. The lemma this paragraph names has no consumers.

*The arithmetic was checked and the item was not, which is how the mis-siting survived a
review.*

Worth checking rather than assuming: the tape bound comes from where the sixth-moment
concentration argument stops working, and nothing forced it to sit above the parameter the
statement actually uses. -/

theorem signingLimit_le_tapeBound : signingLimit ≤ 5 * 2 ^ 62 := by
  simp only [signingLimit]
  norm_num

end SlhDsaSecurity.ForsLeaveOneOut

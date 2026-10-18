import XmssSecurity.Proof.Generic.CacheAgreement
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! A collision created only by divergent executions can pay for its own
acceptance charge. Keep both event transfers in the same coupling to cancel it. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.TargetSum

theorem accepted_event_weighted_probability_le_of_relTriple {α β : Type}
    {source : ProbComp α} {target : ProbComp β}
    (win accepted : α → Prop) (probe hit : β → Prop) (rate : ℝ≥0∞) (hrate : rate ≤ 1)
    (hrel : RelTriple source target (fun left right =>
      (win left → accepted left ∧ hit right) ∧ (probe right → accepted left ∨ hit right))) :
    Pr[win | source] + rate * Pr[probe | target] ≤
      rate * Pr[accepted | source] + Pr[hit | target] := by
  classical
  obtain ⟨coupling, hcoupling⟩ := relTriple_iff_relWP.mp hrel
  have hleft (event : α → Prop) : Pr[event | source] = Pr[event ∘ Prod.fst | coupling.1] := by
    rw [show Pr[event | source] = Pr[event | (𝒟[source] : SPMF α)] from rfl,
      ← probEvent_map, coupling.2.map_fst]
  have hright (event : β → Prop) : Pr[event | target] = Pr[event ∘ Prod.snd | coupling.1] := by
    rw [show Pr[event | target] = Pr[event | (𝒟[target] : SPMF β)] from rfl,
      ← probEvent_map, coupling.2.map_snd]
  rw [hleft win, hleft accepted, hright probe, hright hit]
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add,
    Function.comp_def]
  apply ENNReal.tsum_le_tsum
  intro pair
  by_cases hpair : pair ∈ support coupling.1
  · have hpost := hcoupling pair hpair
    by_cases hwin : win pair.1
    · obtain ⟨haccepted, hhit⟩ := hpost.1 hwin
      by_cases hprobe : probe pair.2 <;> simp only [hwin, haccepted, hhit, hprobe,
        if_true, if_false, mul_zero, add_zero]
      · exact (add_comm _ _).le
      · exact le_add_left le_rfl
    · by_cases haccepted : accepted pair.1
      · by_cases hprobe : probe pair.2 <;> by_cases hhit : hit pair.2 <;>
          simp only [hwin, haccepted, hprobe, hhit, if_true, if_false, mul_zero, zero_add, add_zero]
        all_goals first | exact le_add_right le_rfl | exact le_rfl | exact zero_le
      · by_cases hprobe : probe pair.2
        · have hhit := (hpost.2 hprobe).resolve_left haccepted
          simp only [hwin, haccepted, hprobe, hhit, if_true, if_false, mul_zero, zero_add]
          exact mul_le_of_le_one_left zero_le hrate
        · simp only [hwin, haccepted, hprobe, if_false, mul_zero, zero_add]
          exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hpair]
    simp only [ite_self, mul_zero, add_zero, le_refl]

theorem accepted_event_probability_le_of_relTriple {α β : Type}
    {source : ProbComp α} {target : ProbComp β}
    (win accepted : α → Prop) (probe hit : β → Prop) (rate bound : ℝ≥0∞) (hrate : rate ≤ 1)
    (hrel : RelTriple source target (fun left right =>
      (win left → accepted left ∧ hit right) ∧ (probe right → accepted left ∨ hit right)))
    (hhit : Pr[hit | target] ≤ bound + rate * Pr[probe | target]) :
    Pr[win | source] ≤ bound + rate * Pr[accepted | source] := by
  have h := (accepted_event_weighted_probability_le_of_relTriple win accepted probe hit rate hrate hrel).trans
    (add_le_add le_rfl hhit)
  rw [← add_assoc, add_comm (rate * Pr[accepted | source]) bound] at h
  exact (ENNReal.add_le_add_iff_right (by
    exact mul_ne_top (ne_top_of_le_ne_top (by norm_num) hrate) probEvent_ne_top)).mp h

/-- info: 'XmssSecurity.TargetSum.accepted_event_probability_le_of_relTriple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_event_probability_le_of_relTriple

end XmssSecurity.TargetSum

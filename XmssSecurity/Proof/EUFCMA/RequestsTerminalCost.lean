import XmssSecurity.Proof.EUFCMA.RequestsTerminalPrune

/-! The stopped program saves one charged opportunity on every inactive branch.
The bound applies to any counter increasing by at most one per charged query. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA.Requests

theorem stopInactive_support_budget {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (activity : (OracleWorld + SigningSpec).Domain → Bool) (active : State → Bool) (counter : State → ℕ)
    (hactivity : ∀ input state result, result ∈ support ((impl input).run state) →
      active result.2 = (active state || activity input))
    (hcounter : ∀ input state result, result ∈ support ((impl input).run state) →
      counter result.2 ≤ counter state + if IsCharged input then 1 else 0)
    (fallback : α) (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ) (state : State)
    (hbound : computation.IsQueryBoundP IsCharged budget)
    (result : α × State)
    (hresult : result ∈ support ((simulateQ impl
      (stopInactive activity budget (active state) fallback computation)).run state)) :
    counter result.2 ≤ counter state + budget ∧
      (0 < budget → active result.2 = false → counter result.2 < counter state + budget) ∧
      (active state = true → active result.2 = true) := by
  induction computation using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [stopInactive_pure, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      dsimp only
      exact ⟨by omega, by omega, id⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [stopInactive_query_bind] at hresult
      by_cases hcut : budget = 1 ∧ active state = false ∧ IsCharged input ∧ activity input = false
      · rw [if_pos hcut] at hresult
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        dsimp only
        exact ⟨by omega, by omega, id⟩
      · rw [if_neg hcut, Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [← hactivity input state head hhead] at htail
        have hrest := ih head.1 _ head.2 (hbound.2 head.1) result htail
        have hcount := hcounter input state head hhead
        have hflag := hactivity input state head hhead
        have hinactive (h : active result.2 = false) : active state = false ∧ activity input = false := by
          have hheadFalse : active head.2 = false := Bool.eq_false_iff.mpr (fun htrue => by
            have hfinal := hrest.2.2 htrue
            simp_all)
          rw [hflag, Bool.or_eq_false_iff] at hheadFalse
          exact hheadFalse
        refine ⟨?_, ?_, ?_⟩
        · by_cases hcharged : IsCharged input
          · have hpositive := hbound.1.resolve_left (not_not.mpr hcharged)
            simp only [if_pos hcharged] at hrest hcount
            omega
          · simp only [if_neg hcharged, Nat.add_zero] at hrest hcount
            omega
        · intro hpositive hinactiveFinal
          by_cases hcharged : IsCharged input
          · have hmore : 1 < budget := by
              have hinactive' := hinactive hinactiveFinal
              have hne : budget ≠ 1 := fun h => hcut ⟨h, hinactive'.1, hcharged, hinactive'.2⟩
              omega
            have hstrict := hrest.2.1 (by simp only [if_pos hcharged]; omega) hinactiveFinal
            simp only [if_pos hcharged] at hstrict hcount
            omega
          · have hstrict := hrest.2.1 (by simpa only [if_neg hcharged] using hpositive) hinactiveFinal
            simp only [if_neg hcharged, Nat.add_zero] at hstrict hcount
            omega
        · intro hactive
          apply hrest.2.2
          simp only [hflag, hactive, Bool.true_or]

theorem stopInactive_counter_le_terminal {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (activity : (OracleWorld + SigningSpec).Domain → Bool) (active : State → Bool) (counter : State → ℕ)
    (hactivity : ∀ input state result, result ∈ support ((impl input).run state) →
      active result.2 = (active state || activity input))
    (hcounter : ∀ input state result, result ∈ support ((impl input).run state) →
      counter result.2 ≤ counter state + if IsCharged input then 1 else 0)
    (fallback : α) (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ) (state : State)
    (hpositive : 0 < budget) (hbound : computation.IsQueryBoundP IsCharged budget)
    (result : α × State)
    (hresult : result ∈ support ((simulateQ impl
      (stopInactive activity budget (active state) fallback computation)).run state)) :
    counter result.2 ≤ counter state + (budget - 1) + if active result.2 then 1 else 0 := by
  have h := stopInactive_support_budget impl activity active counter hactivity hcounter
    fallback computation budget state hbound result hresult
  cases hactive : active result.2 <;> simp only [Bool.false_eq_true, if_false, if_true]
  · have := h.2.1 hpositive hactive
    omega
  · omega

/-- info: 'XmssSecurity.EUFCMA.Requests.stopInactive_counter_le_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stopInactive_counter_le_terminal

theorem expected_stopInactive_counter_le {α State : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp))
    (activity : (OracleWorld + SigningSpec).Domain → Bool)
    (hcharged : ∀ input, activity input = true → IsCharged input)
    (active : State → Bool) (counter : State → ℕ)
    (hactivity : ∀ input state result, result ∈ support ((impl input).run state) →
      active result.2 = (active state || activity input))
    (hcounter : ∀ input state result, result ∈ support ((impl input).run state) →
      counter result.2 ≤ counter state + if IsCharged input then 1 else 0)
    (fallback : α) (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ) (state : State)
    (hpositive : 0 < budget) (hbound : computation.IsQueryBoundP IsCharged budget)
    (hzero : counter state = 0) :
    (∑' result, Pr[= result | (simulateQ impl
      (stopInactive activity budget (active state) fallback computation)).run state] *
        (counter result.2 : ℝ≥0∞)) ≤
      ((budget - 1 : ℕ) : ℝ≥0∞) +
        Pr[fun result => active result.2 = true | (simulateQ impl computation).run state] := by
  let program := (simulateQ impl (stopInactive activity budget (active state) fallback computation)).run state
  calc
    _ ≤ ∑' result, Pr[= result | program] *
        (((budget - 1 : ℕ) : ℝ≥0∞) + if active result.2 then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support program
      · apply mul_le_mul' le_rfl
        have h := stopInactive_counter_le_terminal impl activity active counter hactivity hcounter
          fallback computation budget state hpositive hbound result hresult
        rw [hzero, Nat.zero_add] at h
        exact_mod_cast h
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = ((budget - 1 : ℕ) : ℝ≥0∞) + Pr[fun result => active result.2 = true | program] := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul, probEvent_eq_tsum_ite]
      congr 1
      apply tsum_congr
      intro result
      split_ifs <;> simp only [mul_one, mul_zero]
    _ = _ := by
      rw [probEvent_stopInactive_eq impl activity hcharged active hactivity
        (fun result : α × State => active result.2 = true) (fun _ h => h)
        fallback computation budget state hbound]

/-- info: 'XmssSecurity.EUFCMA.Requests.expected_stopInactive_counter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expected_stopInactive_counter_le

end XmssSecurity.EUFCMA.Requests

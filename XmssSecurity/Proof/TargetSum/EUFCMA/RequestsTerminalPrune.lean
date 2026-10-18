import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsExpected
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Stop before the last charged query on a branch with no relevant activity.
Events requiring activity retain their probability: after that last query the
shared budget leaves no opportunity to create activity. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

noncomputable def stopInactive {α : Type} (activity : (OracleWorld + Generic.SigningSpec).Domain → Bool)
    (budget : ℕ) (active : Bool) (fallback : α)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    OracleComp (OracleWorld + Generic.SigningSpec) α :=
  OracleComp.recOn computation (fun value _ _ => pure value)
    (fun input _ next budget active =>
      if budget = 1 ∧ active = false ∧ IsCharged input ∧ activity input = false then pure fallback
      else liftM ((OracleWorld + Generic.SigningSpec).query input) >>= fun answer =>
        next answer (if IsCharged input then budget - 1 else budget) (active || activity input)) budget active

@[simp] theorem stopInactive_pure {α : Type} (activity) (budget : ℕ) (active : Bool)
    (fallback value : α) : stopInactive activity budget active fallback (pure value) = pure value := rfl

theorem stopInactive_query_bind {α : Type} (activity) (budget : ℕ) (active : Bool) (fallback : α)
    (input : (OracleWorld + Generic.SigningSpec).Domain)
    (next : (OracleWorld + Generic.SigningSpec).Range input → OracleComp (OracleWorld + Generic.SigningSpec) α) :
    stopInactive activity budget active fallback (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next) =
      if budget = 1 ∧ active = false ∧ IsCharged input ∧ activity input = false then pure fallback
      else liftM ((OracleWorld + Generic.SigningSpec).query input) >>= fun answer =>
        stopInactive activity (if IsCharged input then budget - 1 else budget) (active || activity input)
          fallback (next answer) := rfl

theorem stopInactive_isQueryBound {α : Type} (activity) (budget : ℕ) (active : Bool) (fallback : α)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (hbound : computation.IsQueryBoundP IsCharged budget) :
    (stopInactive activity budget active fallback computation).IsQueryBoundP IsCharged budget := by
  induction computation using OracleComp.inductionOn generalizing budget active with
  | pure value => simp
  | query_bind input next ih =>
      rw [stopInactive_query_bind]
      split
      · simp
      · rw [isQueryBoundP_query_bind_iff] at hbound ⊢
        exact ⟨hbound.1, fun answer => ih answer _ _ (hbound.2 answer)⟩

theorem zero_budget_preserves_activity {α State : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT State ProbComp))
    (activity : (OracleWorld + Generic.SigningSpec).Domain → Bool)
    (hcharged : ∀ input, activity input = true → IsCharged input)
    (active : State → Bool)
    (hstep : ∀ input state result, result ∈ support ((impl input).run state) →
      active result.2 = (active state || activity input))
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : State)
    (hbound : computation.IsQueryBoundP IsCharged 0)
    (result : α × State) (hresult : result ∈ support ((simulateQ impl computation).run state)) :
    active result.2 = active state := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hresult ▸ rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hnot : ¬IsCharged input := hbound.1.resolve_right (by omega)
      have hinactive : activity input = false := Bool.eq_false_iff.mpr (fun h => hnot (hcharged input h))
      rw [Generic.Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [ih head.1 head.2 (by simpa only [if_neg hnot, Nat.sub_zero] using hbound.2 head.1) result htail,
        hstep input state head hhead, hinactive, Bool.or_false]

theorem probEvent_stopInactive_eq {α State : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec) (StateT State ProbComp))
    (activity : (OracleWorld + Generic.SigningSpec).Domain → Bool)
    (hcharged : ∀ input, activity input = true → IsCharged input)
    (active : State → Bool)
    (hstep : ∀ input state result, result ∈ support ((impl input).run state) →
      active result.2 = (active state || activity input))
    (event : α × State → Prop) (hgate : ∀ result, event result → active result.2 = true)
    (fallback : α) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (budget : ℕ) (state : State)
    (hbound : computation.IsQueryBoundP IsCharged budget) :
    Pr[event | (simulateQ impl (stopInactive activity budget (active state) fallback computation)).run state] =
      Pr[event | (simulateQ impl computation).run state] := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [stopInactive_query_bind]
      split
      · rename_i hcut
        obtain ⟨rfl, hinactive, hinput, hactivity⟩ := hcut
        have hzero : Pr[event | (simulateQ impl
            (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next)).run state] = 0 := by
          apply probEvent_eq_zero
          intro result hresult hevent
          rw [Generic.Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨head, hhead, htail⟩ := hresult
          have hfinal := zero_budget_preserves_activity impl activity hcharged active hstep (next head.1) head.2
            (by simpa only [if_pos hinput, Nat.sub_self] using hbound.2 head.1) result htail
          rw [hstep input state head hhead, hinactive, hactivity] at hfinal
          have := hgate result hevent
          simp_all
        rw [hzero]
        apply probEvent_eq_zero
        intro result hresult hevent
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        have := hgate (fallback, state) hevent
        simp_all
      · rw [Generic.Direct.run_simulateQ_query_bind, Generic.Direct.run_simulateQ_query_bind,
          probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro head
        by_cases hhead : head ∈ support ((impl input).run state)
        · rw [← hstep input state head hhead, ih head.1 _ head.2 (hbound.2 head.1)]
        · rw [probOutput_eq_zero_of_not_mem_support hhead, zero_mul, zero_mul]

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.probEvent_stopInactive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_stopInactive_eq

end XmssSecurity.TargetSum.EUFCMA.Requests

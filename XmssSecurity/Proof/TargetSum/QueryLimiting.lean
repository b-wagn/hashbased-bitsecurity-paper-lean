import XmssSecurity.Proof.Common.QueryCounting
import XmssSecurity.Proof.Generic.ConsistentQueryBound
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Stop before an unaffordable query, retaining both the observed prefix and unused fuel.
The transparency theorem uses a bound on supported executions, so deterministic oracle
answers need not satisfy a stronger syntactic bound. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.QueryLimiting

variable {Index : Type} {spec : OracleSpec Index} {α : Type}

noncomputable def limit (selected : Index → Prop) [DecidablePred selected]
    (fuel : Nat) (computation : OracleComp spec α) : OracleComp spec (Option α × Nat) :=
  OracleComp.recOn computation (fun value fuel => pure (some value, fuel))
    (fun input _ next fuel =>
      if selected input ∧ fuel = 0 then pure (none, fuel)
      else liftM (spec.query input) >>= fun answer =>
        next answer (fuel - if selected input then 1 else 0)) fuel

variable (selected : Index → Prop) [DecidablePred selected]

theorem limit_pure (fuel : Nat) (value : α) :
    limit selected fuel (pure value : OracleComp spec α) = pure (some value, fuel) := rfl

theorem limit_query_bind (fuel : Nat) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) :
    limit selected fuel (liftM (spec.query input) >>= next) =
      if selected input ∧ fuel = 0 then pure (none, fuel)
      else liftM (spec.query input) >>= fun answer =>
        limit selected (fuel - if selected input then 1 else 0) (next answer) := rfl

theorem limit_preserves_queryBound (other : Index → Prop) [DecidablePred other]
    (fuel bound : Nat) (computation : OracleComp spec α)
    (hbound : computation.IsQueryBoundP other bound) :
    (limit selected fuel computation).IsQueryBoundP other bound := by
  induction computation using OracleComp.inductionOn generalizing fuel bound with
  | pure value => simp [limit_pure]
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [limit_query_bind]
      by_cases hstop : selected input ∧ fuel = 0
      · rw [if_pos hstop]
        simp
      · rw [if_neg hstop, OracleComp.isQueryBoundP_query_bind_iff]
        exact ⟨hbound.1, fun answer => ih answer _ _ (hbound.2 answer)⟩

section Trace

variable {Log : Type} [EmptyCollection Log] [Append Log] [LawfulAppend Log]
    (impl : QueryImpl spec (WriterT Log ProbComp))
    (measure : Log → Nat)
    (measure_empty : measure ∅ = 0)
    (measure_append : ∀ left right, measure (left ++ right) = measure left + measure right)
    (measure_query : ∀ input result, result ∈ support (impl input).run →
      measure result.2 = if selected input then 1 else 0)

theorem run_trace_query_bind (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) :
    (simulateQ impl (liftM (spec.query input) >>= next)).run =
      (impl input).run >>= fun head =>
        (fun tail => (tail.1, head.2 ++ tail.2)) <$>
          (simulateQ impl (next head.1)).run := by
  simp [simulateQ_bind]

/-- Successful limited runs retain an exact supported run of the original computation. -/
theorem limit_success_support (fuel : Nat) (computation : OracleComp spec α)
    (result : (Option α × Nat) × Log) (value : α)
    (hresult : result ∈ support (simulateQ impl (limit selected fuel computation)).run)
    (hvalue : result.1.1 = some value) :
    (value, result.2) ∈ support (simulateQ impl computation).run := by
  induction computation using OracleComp.inductionOn generalizing fuel result value with
  | pure output =>
      simp only [limit_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp only [Option.some.injEq] at hvalue
      subst value
      simp
  | query_bind input next ih =>
      rw [limit_query_bind] at hresult
      by_cases hstop : selected input ∧ fuel = 0
      · rw [if_pos hstop] at hresult
        simp only [simulateQ_pure, WriterT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        cases hvalue
      · rw [if_neg hstop, run_trace_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [support_map] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        have horiginal := ih head.1 _ tail value htail hvalue
        rw [run_trace_query_bind, mem_support_bind_iff]
        refine ⟨head, hhead, ?_⟩
        rw [support_map]
        exact ⟨(value, tail.2), horiginal, rfl⟩

include measure_empty measure_append measure_query

/-- The limiter is invisible when every supported complete execution fits the budget. -/
theorem simulate_limit_eq (fuel : Nat) (computation : OracleComp spec α)
    (hbound : ∀ result ∈ support (simulateQ impl computation).run, measure result.2 ≤ fuel) :
    (simulateQ impl (limit selected fuel computation)).run =
      (fun result => ((some result.1, fuel - measure result.2), result.2)) <$>
        (simulateQ impl computation).run := by
  induction computation using OracleComp.inductionOn generalizing fuel with
  | pure value => simp [limit_pure, measure_empty]
  | query_bind input next ih =>
      have hcont (head) (hhead : head ∈ support (impl input).run)
          (tail) (htail : tail ∈ support (simulateQ impl (next head.1)).run) :
          (if selected input then 1 else 0) + measure tail.2 ≤ fuel := by
        have h := hbound (tail.1, head.2 ++ tail.2) (by
          rw [run_trace_query_bind, mem_support_bind_iff]
          exact ⟨head, hhead, by rw [support_map]; exact ⟨tail, htail, rfl⟩⟩)
        rwa [measure_append, measure_query input head hhead] at h
      have haffordable : ¬(selected input ∧ fuel = 0) := by
        obtain ⟨head, hhead⟩ := Generic.probComp_support_nonempty (impl input).run
        obtain ⟨tail, htail⟩ := Generic.probComp_support_nonempty (simulateQ impl (next head.1)).run
        have h := hcont head hhead tail htail
        rintro ⟨hselected, rfl⟩
        simp only [if_pos hselected] at h
        omega
      rw [limit_query_bind, if_neg haffordable, run_trace_query_bind,
        run_trace_query_bind, map_bind]
      refine bind_congr_of_forall_mem_support _ fun head hhead => ?_
      rw [ih head.1 (fuel - if selected input then 1 else 0) (fun tail htail => by
        have h := hcont head hhead tail htail
        omega), Functor.map_map, Functor.map_map]
      congr 1
      funext tail
      simp only [measure_append, measure_query input head hhead]
      congr 2
      omega

/-- Every retained trace fits, including the prefix of an aborted execution. -/
theorem limit_trace_budget (fuel : Nat) (computation : OracleComp spec α)
    (result : (Option α × Nat) × Log)
    (hresult : result ∈ support (simulateQ impl (limit selected fuel computation)).run) :
    measure result.2 + result.1.2 = fuel := by
  induction computation using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [limit_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [measure_empty]
  | query_bind input next ih =>
      rw [limit_query_bind] at hresult
      by_cases hstop : selected input ∧ fuel = 0
      · rw [if_pos hstop] at hresult
        simp only [simulateQ_pure, WriterT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        simp [measure_empty]
      · rw [if_neg hstop, run_trace_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [support_map] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        have h := ih head.1 _ tail htail
        change measure (head.2 ++ tail.2) + tail.1.2 = fuel
        rw [measure_append, measure_query input head hhead]
        by_cases hselected : selected input
        · rw [if_pos hselected] at h ⊢
          have hpos : fuel ≠ 0 := fun hzero => hstop ⟨hselected, hzero⟩
          omega
        · rw [if_neg hselected] at h ⊢
          omega

end Trace

/-- info: 'XmssSecurity.TargetSum.QueryLimiting.simulate_limit_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limit_eq

/-- info: 'XmssSecurity.TargetSum.QueryLimiting.limit_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limit_trace_budget

end XmssSecurity.TargetSum.QueryLimiting

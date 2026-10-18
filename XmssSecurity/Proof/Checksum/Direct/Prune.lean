import XmssSecurity.Proof.Checksum.Direct.Basic
import XmssSecurity.Proof.Common.QueryCounting
import XmssSecurity.Proof.Checksum.ConsistentQueryBound
import XmssSecurity.Proof.Checksum.RandomizedStatement

/-!
# Pruning is invisible within the budget

If every reachable execution of a computation makes at most `budget` direct hash queries
(measured by `QueryCounting.counted IsDirectHashQuery`), then `pruneDirect budget` does not change
its simulation under any stateful implementation.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.Direct

theorem run_simulateQ_query_bind {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : σ) :
    (simulateQ impl (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run state =
      (impl input).run state >>= fun r => (simulateQ impl (next r.1)).run r.2 := by
  simp [simulateQ_bind, StateT.run_bind]

theorem run_counted_query_bind {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : σ) :
    (simulateQ impl (QueryCounting.counted IsDirectHashQuery
        (liftM ((OracleWorld + SigningSpec).query input) >>= next))).run state =
      (impl input).run state >>= fun r =>
        (fun q => ((q.1.1, (if IsDirectHashQuery input then 1 else 0) + q.1.2), q.2)) <$>
          (simulateQ impl (QueryCounting.counted IsDirectHashQuery (next r.1))).run r.2 := by
  rw [QueryCounting.counted_query_bind]
  simp [simulateQ_bind, StateT.run_bind]

/-- The support hypothesis passes to each continuation, with the budget reduced by the cost of
the first query. -/
theorem bound_continuation {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (budget : ℕ) (state : σ)
    (hbound : ∀ result ∈ support
      ((simulateQ impl (QueryCounting.counted IsDirectHashQuery
        (liftM ((OracleWorld + SigningSpec).query input) >>= next))).run state),
      result.1.2 ≤ budget)
    (r) (hr : r ∈ support ((impl input).run state)) :
    ∀ result ∈ support
      ((simulateQ impl (QueryCounting.counted IsDirectHashQuery (next r.1))).run r.2),
      (if IsDirectHashQuery input then 1 else 0) + result.1.2 ≤ budget := by
  intro result hresult
  rw [run_counted_query_bind] at hbound
  exact hbound _ ((mem_support_bind_iff _ _ _).mpr
    ⟨r, hr, by rw [support_map]; exact ⟨result, hresult, rfl⟩⟩)

theorem simulateQ_pruneDirect_eq {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ) (state : σ)
    (hbound : ∀ result ∈ support
      ((simulateQ impl (QueryCounting.counted IsDirectHashQuery computation)).run state),
      result.1.2 ≤ budget) :
    (simulateQ impl (pruneDirect budget computation)).run state =
      (simulateQ impl computation).run state := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind input next ih =>
      have hcont := bound_continuation impl input next budget state hbound
      rcases input with (uniformOrHash | request)
      · rcases uniformOrHash with uniformInput | hashInput
        · rw [pruneDirect_uniform_bind, run_simulateQ_query_bind, run_simulateQ_query_bind]
          refine bind_congr_of_forall_mem_support _ fun r hr => ih r.1 budget r.2 fun result hresult => ?_
          simpa using hcont r hr result hresult
        · have hpos : budget ≠ 0 := by
            obtain ⟨r, hr⟩ := probComp_support_nonempty ((impl (.inl (.inr hashInput))).run state)
            obtain ⟨result, hresult⟩ := probComp_support_nonempty
              ((simulateQ impl (QueryCounting.counted IsDirectHashQuery (next r.1))).run r.2)
            have := hcont r hr result hresult
            simp at this
            omega
          rw [pruneDirect_hash_bind, if_neg hpos, run_simulateQ_query_bind, run_simulateQ_query_bind]
          refine bind_congr_of_forall_mem_support _ fun r hr =>
            ih r.1 (budget - 1) r.2 fun result hresult => ?_
          have := hcont r hr result hresult
          simp at this
          omega
      · rw [pruneDirect_sign_bind, run_simulateQ_query_bind, run_simulateQ_query_bind]
        refine bind_congr_of_forall_mem_support _ fun r hr => ih r.1 budget r.2 fun result hresult => ?_
        simpa using hcont r hr result hresult

/-! ## Logged implementations in the random-oracle model -/

theorem run_logged_query_bind {β : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
        (simulateQ impl (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run).run cache =
      (simulateQ romImpl (impl input).run).run cache >>= fun p =>
        (fun q => ((q.1.1, p.1.2 ++ q.1.2), q.2)) <$>
          (simulateQ romImpl (simulateQ impl (next p.1.1)).run).run p.2 := by
  simp [simulateQ_bind, StateT.run_bind]

theorem run_logged_counted_query_bind {β : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (simulateQ impl (QueryCounting.counted IsDirectHashQuery
        (liftM ((OracleWorld + SigningSpec).query input) >>= next))).run).run cache =
      (simulateQ romImpl (impl input).run).run cache >>= fun p =>
        (fun q => (((q.1.1.1, (if IsDirectHashQuery input then 1 else 0) + q.1.1.2),
            p.1.2 ++ q.1.2), q.2)) <$>
          (simulateQ romImpl (simulateQ impl
            (QueryCounting.counted IsDirectHashQuery (next p.1.1))).run).run p.2 := by
  rw [QueryCounting.counted_query_bind]
  simp [simulateQ_bind, StateT.run_bind]

theorem bound_continuation_logged {β : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) β)
    (budget : ℕ) (cache : QueryCache HashSpec)
    (hbound : ∀ result ∈ support
      ((simulateQ romImpl (simulateQ impl (QueryCounting.counted IsDirectHashQuery
        (liftM ((OracleWorld + SigningSpec).query input) >>= next))).run).run cache),
      result.1.1.2 ≤ budget)
    (p) (hp : p ∈ support ((simulateQ romImpl (impl input).run).run cache)) :
    ∀ result ∈ support ((simulateQ romImpl (simulateQ impl
        (QueryCounting.counted IsDirectHashQuery (next p.1.1))).run).run p.2),
      (if IsDirectHashQuery input then 1 else 0) + result.1.1.2 ≤ budget := by
  intro result hresult
  rw [run_logged_counted_query_bind] at hbound
  exact hbound _ ((mem_support_bind_iff _ _ _).mpr
    ⟨p, hp, by rw [support_map]; exact ⟨result, hresult, rfl⟩⟩)

/-- `simulateQ_pruneDirect_eq` for a query-logging implementation run in the random-oracle
model. -/
theorem simulateQ_pruneDirect_eq_logged {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ)
    (cache : QueryCache HashSpec)
    (hbound : ∀ result ∈ support
      ((simulateQ romImpl (simulateQ impl
        (QueryCounting.counted IsDirectHashQuery computation)).run).run cache),
      result.1.1.2 ≤ budget) :
    (simulateQ romImpl (simulateQ impl (pruneDirect budget computation)).run).run cache =
      (simulateQ romImpl (simulateQ impl computation).run).run cache := by
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value => rfl
  | query_bind input next ih =>
      have hcont := bound_continuation_logged impl input next budget cache hbound
      rcases input with (uniformOrHash | request)
      · rcases uniformOrHash with uniformInput | hashInput
        · rw [pruneDirect_uniform_bind, run_logged_query_bind, run_logged_query_bind]
          refine bind_congr_of_forall_mem_support _ fun p hp => ?_
          rw [ih p.1.1 budget p.2 fun result hresult => by simpa using hcont p hp result hresult]
        · have hpos : budget ≠ 0 := by
            obtain ⟨p, hp⟩ := probComp_support_nonempty
              ((simulateQ romImpl (impl (.inl (.inr hashInput))).run).run cache)
            obtain ⟨result, hresult⟩ := probComp_support_nonempty
              ((simulateQ romImpl (simulateQ impl
                (QueryCounting.counted IsDirectHashQuery (next p.1.1))).run).run p.2)
            have := hcont p hp result hresult
            simp at this
            omega
          rw [pruneDirect_hash_bind, if_neg hpos, run_logged_query_bind, run_logged_query_bind]
          refine bind_congr_of_forall_mem_support _ fun p hp => ?_
          rw [ih p.1.1 (budget - 1) p.2 fun result hresult => by
            have := hcont p hp result hresult
            simp at this
            omega]
      · rw [pruneDirect_sign_bind, run_logged_query_bind, run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun p hp => ?_
        rw [ih p.1.1 budget p.2 fun result hresult => by simpa using hcont p hp result hresult]

end XmssSecurity.Checksum.Direct

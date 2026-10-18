import XmssSecurity.Proof.Generic.Direct.Prune
import XmssSecurity.Proof.Checksum.NoSign.Forwarding
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-!
# Pruning at a weighted budget

`pruneWeighted signCost budget` truncates a program at a budget in which a direct hash query costs
one unit and a signing request `signCost` units: a query the remaining budget cannot pay is
answered by `default` (`none` for a request) without being made. The pruned program has at most
`budget` direct hash queries, and no signing request when `budget < signCost`. Every execution
of a logged implementation whose direct hash queries and logged requests fit the budget is an
execution of the pruned program (`simulateQ_pruneWeighted_eq_logged`).
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

/-- The program truncated at a weighted budget. -/
noncomputable def pruneWeighted {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    OracleComp (OracleWorld + Generic.SigningSpec) α :=
  OracleComp.recOn computation (fun value _ => pure value)
    (fun input _ ih budget => match input with
      | .inl (.inr hashInput) =>
          if budget = 0 then ih default 0
          else liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inr hashInput))) >>= fun answer =>
            ih answer (budget - 1)
      | .inl (.inl uniformInput) =>
          liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inl uniformInput))) >>= fun answer =>
            ih answer budget
      | .inr request =>
          if budget < signCost then ih none budget
          else liftM ((OracleWorld + Generic.SigningSpec).query (.inr request)) >>= fun answer =>
            ih answer (budget - signCost)) budget

theorem pruneWeighted_pure {α : Type} (signCost budget : ℕ) (value : α) :
    pruneWeighted signCost budget (pure value : OracleComp (OracleWorld + Generic.SigningSpec) α) =
      pure value := rfl

theorem pruneWeighted_hash_bind {α : Type} (signCost budget : ℕ) (hashInput : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + Generic.SigningSpec) α) :
    pruneWeighted signCost budget
        (liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inr hashInput))) >>= next) =
      if budget = 0 then pruneWeighted signCost 0 (next default)
      else liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inr hashInput))) >>= fun answer =>
        pruneWeighted signCost (budget - 1) (next answer) := rfl

theorem pruneWeighted_uniform_bind {α : Type} (signCost budget : ℕ)
    (uniformInput : unifSpec.Domain)
    (next : unifSpec.Range uniformInput → OracleComp (OracleWorld + Generic.SigningSpec) α) :
    pruneWeighted signCost budget
        (liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inl uniformInput))) >>= next) =
      liftM ((OracleWorld + Generic.SigningSpec).query (.inl (.inl uniformInput))) >>= fun answer =>
        pruneWeighted signCost budget (next answer) := rfl

theorem pruneWeighted_sign_bind {α : Type} (signCost budget : ℕ) (request : Generic.SignRequest)
    (next : Option Generic.Signature → OracleComp (OracleWorld + Generic.SigningSpec) α) :
    pruneWeighted signCost budget
        (liftM ((OracleWorld + Generic.SigningSpec).query (.inr request)) >>= next) =
      if budget < signCost then pruneWeighted signCost budget (next none)
      else liftM ((OracleWorld + Generic.SigningSpec).query (.inr request)) >>= fun answer =>
        pruneWeighted signCost (budget - signCost) (next answer) := rfl

/-! ## The pruned program is bounded -/

theorem pruneWeighted_isQueryBoundP_direct {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    (pruneWeighted signCost budget computation).IsQueryBoundP Generic.Direct.IsDirectHashQuery budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => simp [pruneWeighted_pure]
  | query_bind input next ih =>
      rcases input with (uniformInput | hashInput) | request
      · rw [pruneWeighted_uniform_bind, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun answer => by simpa using ih answer budget⟩
      · rw [pruneWeighted_hash_bind]
        split_ifs with hzero
        · subst hzero
          exact ih default 0
        · rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inr (Nat.pos_of_ne_zero hzero), fun answer => by
            simpa using ih answer (budget - 1)⟩
      · rw [pruneWeighted_sign_bind]
        split_ifs with hlow
        · exact ih none budget
        · rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp), fun answer => by
            simpa using (ih answer (budget - signCost)).mono (Nat.sub_le _ _)⟩

theorem pruneWeighted_isQueryBoundP_sign {α : Type} (signCost budget : ℕ)
    (hbudget : budget < signCost) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) :
    (pruneWeighted signCost budget computation).IsQueryBoundP IsSignQuery 0 := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => simp [pruneWeighted_pure]
  | query_bind input next ih =>
      rcases input with (uniformInput | hashInput) | request
      · rw [pruneWeighted_uniform_bind, isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
          simpa [IsSignQuery] using ih answer budget hbudget⟩
      · rw [pruneWeighted_hash_bind]
        split_ifs with hzero
        · exact ih default 0 (by omega)
        · rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
            simpa [IsSignQuery] using ih answer (budget - 1) (by omega)⟩
      · rw [pruneWeighted_sign_bind, if_pos hbudget]
        exact ih none budget hbudget

/-! ## Pruning is invisible within the budget -/

/-- The world queries of `impl` log nothing and each signing request logs exactly one entry. -/
def LogsRequests
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec)
      (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld))) : Prop :=
  (∀ input cache, ∀ step ∈ support ((simulateQ Generic.romImpl (impl (.inl input)).run).run cache),
    step.1.2 = []) ∧
  (∀ request cache, ∀ step ∈ support ((simulateQ Generic.romImpl (impl (.inr request)).run).run cache),
    step.1.2.length = 1)

theorem simulateQ_pruneWeighted_eq_logged {α : Type}
    (impl : QueryImpl (OracleWorld + Generic.SigningSpec)
      (WriterT (QueryLog Generic.SigningSpec) (OracleComp OracleWorld)))
    (himpl : LogsRequests impl) (signCost : ℕ)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (budget : ℕ)
    (cache : QueryCache HashSpec)
    (hbound : ∀ result ∈ support
      ((simulateQ Generic.romImpl (simulateQ impl
        (QueryCounting.counted Generic.Direct.IsDirectHashQuery computation)).run).run cache),
      result.1.1.2 + signCost * result.1.2.length ≤ budget) :
    (simulateQ Generic.romImpl (simulateQ impl (pruneWeighted signCost budget computation)).run).run
        cache =
      (simulateQ Generic.romImpl (simulateQ impl computation).run).run cache := by
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value => rfl
  | query_bind input next ih =>
      -- Each continuation inherits the bound, less the cost of the first query.
      have hcont : ∀ step ∈ support ((simulateQ Generic.romImpl (impl input).run).run cache),
          ∀ result ∈ support ((simulateQ Generic.romImpl (simulateQ impl
            (QueryCounting.counted Generic.Direct.IsDirectHashQuery (next step.1.1))).run).run step.2),
          (if Generic.Direct.IsDirectHashQuery input then 1 else 0) + result.1.1.2 +
            signCost * (step.1.2.length + result.1.2.length) ≤ budget := by
        intro step hstep result hresult
        have := Generic.Direct.bound_continuation_logged impl input next budget cache
          (fun result hresult => (Nat.le_add_right _ _).trans (hbound result hresult))
        rw [Generic.Direct.run_logged_counted_query_bind] at hbound
        have hmem := hbound _ ((mem_support_bind_iff _ _ _).mpr
          ⟨step, hstep, by rw [support_map]; exact ⟨result, hresult, rfl⟩⟩)
        simpa [List.length_append, add_assoc] using hmem
      have hnonempty : ∃ step ∈ support ((simulateQ Generic.romImpl (impl input).run).run cache),
          ∃ result ∈ support ((simulateQ Generic.romImpl (simulateQ impl
            (QueryCounting.counted Generic.Direct.IsDirectHashQuery (next step.1.1))).run).run step.2),
            True := by
        obtain ⟨step, hstep⟩ := Generic.probComp_support_nonempty
          ((simulateQ Generic.romImpl (impl input).run).run cache)
        obtain ⟨result, hresult⟩ := Generic.probComp_support_nonempty
          ((simulateQ Generic.romImpl (simulateQ impl
            (QueryCounting.counted Generic.Direct.IsDirectHashQuery (next step.1.1))).run).run step.2)
        exact ⟨step, hstep, result, hresult, trivial⟩
      rcases input with (uniformInput | hashInput) | request
      · rw [pruneWeighted_uniform_bind, Generic.Direct.run_logged_query_bind,
          Generic.Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun step hstep => ?_
        have hlog := himpl.1 (.inl uniformInput) cache step hstep
        rw [ih step.1.1 budget step.2 fun result hresult => by
          have := hcont step hstep result hresult
          simp only [hlog, List.length_nil, zero_add] at this
          simpa using this]
      · obtain ⟨step₀, hstep₀, result₀, hresult₀, -⟩ := hnonempty
        have hpos : budget ≠ 0 := by
          have := hcont step₀ hstep₀ result₀ hresult₀
          simp at this
          omega
        rw [pruneWeighted_hash_bind, if_neg hpos, Generic.Direct.run_logged_query_bind,
          Generic.Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun step hstep => ?_
        have hlog := himpl.1 (.inr hashInput) cache step hstep
        rw [ih step.1.1 (budget - 1) step.2 fun result hresult => by
          have := hcont step hstep result hresult
          simp only [hlog, List.length_nil, zero_add] at this
          simp at this
          omega]
      · obtain ⟨step₀, hstep₀, result₀, hresult₀, -⟩ := hnonempty
        have hlog₀ := himpl.2 request cache step₀ hstep₀
        have henough : ¬ budget < signCost := by
          have := hcont step₀ hstep₀ result₀ hresult₀
          rw [hlog₀] at this
          simp at this
          nlinarith
        rw [pruneWeighted_sign_bind, if_neg henough, Generic.Direct.run_logged_query_bind,
          Generic.Direct.run_logged_query_bind]
        refine bind_congr_of_forall_mem_support _ fun step hstep => ?_
        have hlog := himpl.2 request cache step hstep
        rw [ih step.1.1 (budget - signCost) step.2 fun result hresult => by
          have := hcont step hstep result hresult
          rw [hlog] at this
          simp at this
          rw [mul_add, mul_one] at this
          omega]

end XmssSecurity.Checksum.NoSign

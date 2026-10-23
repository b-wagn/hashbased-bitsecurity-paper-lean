import SlhDsaSecurity.Proof.SignedWatch

/-!
# Capping a computation at a weighted query budget

The total budget `HasTotalBudget` is a probability-one statement about the real game. A charge
taken in a *blind* game needs the adversary's query count bounded there too, and after the blind
game's bad event its answers can be inconsistent with anything the real game produces — an
adversary that notices may then query without limit. So the adversary is capped.

`capComp weight fallback limit oa` runs `oa` until the next query would take its weighted count
past `limit`, and then returns `fallback`. Two facts make it usable:

* **On every handler, the capped run's weighted cost is at most `limit`** (`cost_capComp_le`) —
  provided the handler's state reports the cost, step by step.
* **Where the uncapped run never exceeds `limit`, capping changes nothing** (`evalDist_capComp`).

The second is applied at the real game, where the budget says the cap never fires; the first at
the blind game, where nothing else bounds the count.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CapComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- **Truncate a computation once its weighted queries would exceed the limit.** -/
noncomputable def capComp (weight : ι → Nat) (fallback : α) :
    Nat → OracleComp spec α → OracleComp spec α :=
  fun limit oa => OracleComp.construct (C := fun _ => Nat → OracleComp spec α)
    (fun value _ => pure value)
    (fun t _ rest remaining =>
      if weight t ≤ remaining then
        liftM (spec.query t) >>= fun answer => rest answer (remaining - weight t)
      else pure fallback) oa limit

theorem capComp_pure (weight : ι → Nat) (fallback : α) (limit : Nat) (value : α) :
    capComp weight fallback limit (pure value : OracleComp spec α) = pure value := rfl

theorem capComp_query_bind (weight : ι → Nat) (fallback : α) (limit : Nat) (t : ι)
    (next : spec.Range t → OracleComp spec α) :
    capComp weight fallback limit (liftM (spec.query t) >>= next) =
      if weight t ≤ limit then
        liftM (spec.query t) >>= fun answer => capComp weight fallback (limit - weight t)
          (next answer)
      else pure fallback := rfl

variable {S : Type}

/-- A handler whose state reports the weighted cost, query by query. -/
def ReportsCost (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) : Prop :=
  ∀ (t : ι) (state : S), ∀ z ∈ support ((impl t).run state), cost z.2 = cost state + weight t

/-- **The capped run's weighted cost is at most the limit, at any handler.** -/
theorem cost_capComp_le (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) (fallback : α) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S),
      ∀ z ∈ support ((simulateQ impl (capComp weight fallback limit oa)).run state),
        cost z.2 ≤ cost state + limit := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro limit state z hz
    rw [capComp_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    dsimp only
    omega
  | query_bind t next ih =>
    intro limit state z hz
    rw [capComp_query_bind] at hz
    split_ifs at hz with hweight
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨step, hstep, hrest⟩ := hz
      have := ih step.1 (limit - weight t) step.2 z hrest
      have hstepCost := hcost t state step hstep
      omega
    · rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      dsimp only
      omega

/-- The cost only grows along a run. -/
theorem cost_run_ge (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost) :
    ∀ (oa : OracleComp spec α) (state : S),
      ∀ z ∈ support ((simulateQ impl oa).run state), cost state ≤ cost z.2 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    have := ih step.1 step.2 z hrest
    have hstepCost := hcost t state step hstep
    omega

/-- A run of a handler that never fails never fails. -/
theorem run_neverFails (impl : QueryImpl spec (StateT S ProbComp))
    (hfail : ∀ (t : ι) (state : S), Pr[⊥ | (impl t).run state] = 0) :
    ∀ (oa : OracleComp spec α) (state : S), Pr[⊥ | (simulateQ impl oa).run state] = 0 := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => intro state; simp
  | query_bind t next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact probFailure_bind_eq_zero_iff _ _ |>.mpr ⟨hfail t state, fun step _ => ih _ _⟩

/-- A computation that never fails has an outcome. -/
theorem exists_mem_support {β : Type} (mx : ProbComp β) (hfail : Pr[⊥ | mx] = 0) :
    ∃ x, x ∈ support mx := by
  by_contra hnone
  simp only [not_exists] at hnone
  have hone := tsum_probOutput_eq_one' hfail
  rw [show (∑' x, Pr[= x | mx]) = ∑' x, (0 : ℝ≥0∞) from
    tsum_congr fun x => probOutput_eq_zero_of_not_mem_support (hnone x), tsum_zero] at hone
  exact zero_ne_one hone

/-- A bind is determined by its continuation on the support. -/
theorem evalDist_bind_congr_support {β γ : Type} (oa : ProbComp β) (f g : β → ProbComp γ)
    (h : ∀ a ∈ support oa, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[oa >>= f] x = Pr[= x | oa >>= f] from (probOutput_def _ _).symm,
    show 𝒟[oa >>= g] x = Pr[= x | oa >>= g] from (probOutput_def _ _).symm,
    probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  by_cases hmem : a ∈ support oa
  · rw [show Pr[= x | f a] = Pr[= x | g a] from by
      rw [probOutput_def, probOutput_def, h a hmem]]
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-- **Where the uncapped run stays within the limit, capping changes nothing.** -/
theorem evalDist_capComp (impl : QueryImpl spec (StateT S ProbComp)) (weight : ι → Nat)
    (cost : S → Nat) (hcost : ReportsCost impl weight cost)
    (hfail : ∀ (t : ι) (state : S), Pr[⊥ | (impl t).run state] = 0) (fallback : α) :
    ∀ (oa : OracleComp spec α) (limit : Nat) (state : S),
      (∀ z ∈ support ((simulateQ impl oa).run state), cost z.2 ≤ cost state + limit) →
        𝒟[(simulateQ impl (capComp weight fallback limit oa)).run state] =
          𝒟[(simulateQ impl oa).run state] := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure value => intro limit state _; rfl
  | query_bind t next ih =>
    intro limit state hbound
    rw [capComp_query_bind]
    split_ifs with hweight
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine evalDist_bind_congr_support _ _ _ fun step hstep => ?_
      · refine ih step.1 (limit - weight t) step.2 fun z hz => ?_
        have hwhole : z ∈ support ((simulateQ impl (liftM (spec.query t) >>= next)).run state) := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
          exact ⟨step, hstep, hz⟩
        have := hbound z hwhole
        have hstepCost := hcost t state step hstep
        omega
    · exfalso
      obtain ⟨step, hstep⟩ := exists_mem_support _ (hfail t state)
      obtain ⟨z, hz⟩ := exists_mem_support _ (run_neverFails impl hfail (next step.1) step.2)
      have hwhole : z ∈ support ((simulateQ impl (liftM (spec.query t) >>= next)).run state) := by
        rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
        exact ⟨step, hstep, hz⟩
      have h1 := hbound z hwhole
      have h2 := cost_run_ge impl weight cost hcost (next step.1) step.2 z hz
      have h3 := hcost t state step hstep
      omega

end SlhDsaSecurity.CapComp

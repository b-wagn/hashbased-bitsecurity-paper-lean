import SlhDsaSecurity.Proof.TrackedQueries

/-!
# Two handlers that part company only once the bad flag is set

`BlindComparison.prob_touched_eq` and `TrackedQueries.prob_meets_eq` compare **one** computation
run against **two caches** that agree off a set. That is the right shape when the only thing the
secret touches is what was programmed before the run. It is the wrong shape when the secret is
read by the game itself — here, by the signer, which derives every randomiser by querying
`Hashing.randomizerInput SK.prf PK.seed framed`. Then the two games differ in what their
*handlers do*, not in what their caches hold, and no agreement of caches expresses it.

This file is that comparison at the handler. Two handlers, over possibly different state types,
a bad flag on each, and a relation between states. The hypotheses say:

* the relation decides the flag the same way on both sides;
* the flag is sticky — no step of either handler clears it;
* neither handler fails;
* **at every query from an unflagged state, either that query flags the run on both sides, or
  the two steps are the same step** — the right handler's step law being the left handler's
  pushed forward along a deterministic `transfer`, which also carries the relation forward.

The disjunction in the last one is not slack. In the application the flag is set *by* a query:
the adversary asks at a `PRF_msg` input, and that is the whole event. A hypothesis asking the
two steps to agree at every unflagged state would therefore be false at exactly the step the
charge is about. What rescues it is that at such a step there is nothing left to compare —
both runs are already decided — which is the same observation `TrackedQueries.prob_meets_eq`
makes at a query inside its set, here read at the query rather than at the cache.

The conclusion is an **equality** of the probability of ending flagged. That it is an equality
and not an inequality is the whole point, and the reason is the one
`TrackedQueries.prob_meets_real_eq_blind`'s docstring gives: the flag is what the budget pays
for, and an identical-until-bad hop stated as an inequality would ask the budget for a second
`Θ(q / 2 ^ 128)` that does not exist.

`transfer` is deterministic on purpose. A general coupling would be the honest abstraction, but
the application does not need one: the blind game's state is a *function* of the real game's —
its cache with the secret-bearing entries moved into a side table — so the pushforward form is
both enough and far cheaper to discharge.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.HandlerComparison

variable {ι : Type} {spec : OracleSpec ι} {σ τ : Type}

/-! ## Two facts about a single handler

Both are the shape `TrackedQueries` proves for its own oracle, stated once for an arbitrary
handler because the comparison needs them on each side. -/

/-- **A handler whose every step is total gives a total run.** -/
theorem run_neverFails (impl : QueryImpl spec (StateT σ ProbComp))
    (hfail : ∀ (queried : spec.Domain) (state : σ), Pr[⊥ | (impl queried).run state] = 0)
    {α : Type} (computation : OracleComp spec α) (state : σ) :
    Pr[⊥ | (simulateQ impl computation).run state] = 0 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [simulateQ_pure, StateT.run_pure]; simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probFailure_bind_eq_add_tsum,
      hfail queried state, zero_add]
    simp [ih]

/-- **A sticky flag survives a run.** -/
theorem bad_persists (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hsticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((impl queried).run state), bad step.2)
    {α : Type} (computation : OracleComp spec α) :
    ∀ (state : σ), bad state →
      ∀ result ∈ support ((simulateQ impl computation).run state), bad result.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hbad result hresult
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]
    exact hbad
  | query_bind queried next ih =>
    intro state hbad result hresult
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    exact ih step.1 step.2 (hsticky queried state hbad step hstep) result hrest

/-- **Once flagged, the run ends flagged with probability one.** -/
theorem prob_bad_one (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hfail : ∀ (queried : spec.Domain) (state : σ), Pr[⊥ | (impl queried).run state] = 0)
    (hsticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((impl queried).run state), bad step.2)
    {α : Type} (computation : OracleComp spec α) (state : σ) (hbad : bad state) :
    Pr[fun result : α × σ => bad result.2 | (simulateQ impl computation).run state] = 1 :=
  probEvent_eq_one ⟨run_neverFails impl hfail computation state,
    bad_persists impl bad hsticky computation state hbad⟩

/-! ## The comparison -/

/-- Equal laws stay equal under a continuation. -/
theorem evalDist_bind_congr {α β : Type} {left right : ProbComp α} (hlaw : 𝒟[left] = 𝒟[right])
    (next : α → ProbComp β) : 𝒟[left >>= next] = 𝒟[right >>= next] := by
  rw [evalDist_bind, evalDist_bind, hlaw]

/-- **A step that flags makes the rest of the run certain.** -/
theorem prob_bad_one_of_step (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hfail : ∀ (queried : spec.Domain) (state : σ), Pr[⊥ | (impl queried).run state] = 0)
    (hsticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((impl queried).run state), bad step.2)
    (queried : spec.Domain) (state : σ)
    (hflag : ∀ step ∈ support ((impl queried).run state), bad step.2)
    {α : Type} (next : spec.Range queried → OracleComp spec α) :
    Pr[fun result : α × σ => bad result.2 |
      (impl queried).run state >>= fun step =>
        (simulateQ impl (next step.1)).run step.2] = 1 := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' step, Pr[= step | (impl queried).run state] *
        Pr[fun result : α × σ => bad result.2 | (simulateQ impl (next step.1)).run step.2]
      = ∑' step, Pr[= step | (impl queried).run state] := by
        refine tsum_congr fun step => ?_
        by_cases hmem : step ∈ support ((impl queried).run state)
        · rw [prob_bad_one impl bad hfail hsticky _ step.2 (hflag step hmem), mul_one]
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
    _ = 1 := by
        rw [← probFailure_add_tsum_probOutput ((impl queried).run state), hfail queried state,
          zero_add]

set_option maxHeartbeats 1000000 in
/-- **Two handlers that part company only at a flagging query flag the run equally often.**

The left handler is the game being charged and the right one the game the charge is read at;
`transfer` carries a left state to the right state it corresponds to. At every query, from a
state not yet flagged, one of two things must hold: the query flags the run **on both sides**,
in which case what either handler does with it is irrelevant because the event is already
decided; or the two steps correspond, the right handler's step law being the left's pushed
forward along `transfer`, which also carries the relation forward.

The case split is on the **query**, not on the state, and that is forced rather than convenient:
in the application the flag is set *by* a query — the adversary asking at a `PRF_msg` input —
so a hypothesis that asked the two steps to agree at every unflagged state would be false at
exactly the step that matters.

The conclusion is an **equality** of the probability of ending flagged. That it is an equality
and not an inequality is the whole point, and the reason is the one
`TrackedQueries.prob_meets_real_eq_blind`'s docstring gives: the flag is what the budget pays
for, and an identical-until-bad hop stated as an inequality would ask the budget for a second
`Θ(q / 2 ^ 128)` that does not exist. -/
theorem prob_bad_eq (left : QueryImpl spec (StateT σ ProbComp))
    (right : QueryImpl spec (StateT τ ProbComp))
    (bad : σ → Prop) (bad' : τ → Prop) (rel : σ → τ → Prop)
    (transfer : (queried : spec.Domain) → σ → spec.Range queried → σ → τ)
    (hbadIff : ∀ (state : σ) (state' : τ), rel state state' → (bad state ↔ bad' state'))
    (hleftFail : ∀ (queried : spec.Domain) (state : σ), Pr[⊥ | (left queried).run state] = 0)
    (hrightFail : ∀ (queried : spec.Domain) (state : τ), Pr[⊥ | (right queried).run state] = 0)
    (hleftSticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((left queried).run state), bad step.2)
    (hrightSticky : ∀ (queried : spec.Domain) (state : τ),
      bad' state → ∀ step ∈ support ((right queried).run state), bad' step.2)
    (hstep : ∀ (queried : spec.Domain) (state : σ) (state' : τ), rel state state' → ¬ bad state →
      ((∀ step ∈ support ((left queried).run state), bad step.2) ∧
          (∀ step ∈ support ((right queried).run state'), bad' step.2)) ∨
        (𝒟[(right queried).run state'] =
            𝒟[(fun step : spec.Range queried × σ =>
              (step.1, transfer queried state step.1 step.2)) <$> (left queried).run state] ∧
          ∀ step ∈ support ((left queried).run state),
            rel step.2 (transfer queried state step.1 step.2)))
    {α : Type} (computation : OracleComp spec α) :
    ∀ (state : σ) (state' : τ), rel state state' →
      Pr[fun result : α × σ => bad result.2 | (simulateQ left computation).run state] =
        Pr[fun result : α × τ => bad' result.2 | (simulateQ right computation).run state'] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state state' hrelate
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, probEvent_pure,
      probEvent_pure]
    by_cases hbad : bad state
    · rw [if_pos hbad, if_pos ((hbadIff state state' hrelate).mp hbad)]
    · rw [if_neg hbad, if_neg (fun hbad' => hbad ((hbadIff state state' hrelate).mpr hbad'))]
  | query_bind queried next ih =>
    intro state state' hrelate
    by_cases hbad : bad state
    · -- Already flagged: both sides are certain, whatever either handler does next.
      rw [prob_bad_one left bad hleftFail hleftSticky _ state hbad,
        prob_bad_one right bad' hrightFail hrightSticky _ state'
          ((hbadIff state state' hrelate).mp hbad)]
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind]
      rcases hstep queried state state' hrelate hbad with ⟨hleftFlag, hrightFlag⟩ | ⟨hlaw, hcarry⟩
      · -- A flagging query: the event is decided on both sides before the rest runs.
        rw [prob_bad_one_of_step left bad hleftFail hleftSticky queried state hleftFlag next,
          prob_bad_one_of_step right bad' hrightFail hrightSticky queried state' hrightFlag next]
      · -- An ordinary query: the two steps correspond, so recurse at the transferred state.
        rw [probEvent_congr' (fun _ _ => Iff.rfl)
            (evalDist_bind_congr hlaw
              (fun step => (simulateQ right (next step.1)).run step.2)),
          bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        refine tsum_congr fun step => ?_
        by_cases hmem : step ∈ support ((left queried).run state)
        · exact congrArg _ (ih step.1 step.2 _ (hcarry step hmem))
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

end SlhDsaSecurity.HandlerComparison

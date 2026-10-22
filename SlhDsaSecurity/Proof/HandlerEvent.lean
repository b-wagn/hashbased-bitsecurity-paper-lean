import SlhDsaSecurity.Proof.HandlerComparison

/-!
# Identical until bad, for an event other than the flag

`HandlerComparison.prob_bad_eq` compares two handlers that part company only at a flagging query
and concludes an equality of **the flag's own** probability. That is what the randomiser charge
needs of the flag, and it is not what a game hop needs of everything else: to carry a bound from
one game to the other, the quantity being bounded has to move too.

This is that statement. Same two handlers, same hypotheses, and one more: the event agrees on
related states **where the flag is down**. Nothing is asked of it where the flag is up, because
there the conjunct `¬ bad` already decides it — which is the same observation `prob_bad_eq` makes
at a flagging query, read at the event instead of at the flag.

**Why the `¬ bad` conjunct is in the statement rather than in a hypothesis.** An identical-until-bad
hop gives nothing about the event on flagged runs and cannot: the two games genuinely differ
there. So the event that transfers is the event *intersected with the flag being down*, and a
caller recovers what it wants by charging the flag separately — which is exactly what the flag's
own equality is for. The two lemmas are used together or not at all.

**And nothing here is anti-monotone.** The quantity moved is a probability, not a count, so the
obstruction that defeated the weighed-count step does not arise: there is no gauge, nothing has
to grow, and the induction is the one `prob_bad_eq` already runs.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HandlerEvent

open HandlerComparison

variable {ι : Type} {spec : OracleSpec ι} {σ τ : Type}

/-- **From a flagged state the event-with-the-flag-down is impossible.** -/
theorem prob_event_zero (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hsticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((impl queried).run state), bad step.2)
    {α : Type} (event : α × σ → Prop) (computation : OracleComp spec α) (state : σ)
    (hbad : bad state) :
    Pr[fun result : α × σ => event result ∧ ¬ bad result.2 |
      (simulateQ impl computation).run state] = 0 :=
  probEvent_eq_zero fun result hresult hevent =>
    hevent.2 (bad_persists impl bad hsticky computation state hbad result hresult)

/-- **And a step that flags makes it impossible for the rest of the run.** -/
theorem prob_event_zero_of_step (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hsticky : ∀ (queried : spec.Domain) (state : σ),
      bad state → ∀ step ∈ support ((impl queried).run state), bad step.2)
    (queried : spec.Domain) (state : σ)
    (hflag : ∀ step ∈ support ((impl queried).run state), bad step.2)
    {α : Type} (event : α × σ → Prop) (next : spec.Range queried → OracleComp spec α) :
    Pr[fun result : α × σ => event result ∧ ¬ bad result.2 |
      (impl queried).run state >>= fun step =>
        (simulateQ impl (next step.1)).run step.2] = 0 := by
  refine probEvent_eq_zero fun result hresult hevent => ?_
  rw [mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, hrest⟩ := hresult
  exact hevent.2
    (bad_persists impl bad hsticky _ step.2 (hflag step hstep) result hrest)

set_option maxHeartbeats 1000000 in
/-- **Two handlers that part company only at a flagging query agree on every event, off the
flag.** The hop `prob_bad_eq` was missing: the flag's probability moves by that lemma, and
everything else moves by this one. -/
theorem prob_event_eq (left : QueryImpl spec (StateT σ ProbComp))
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
    {α : Type} (event : α × σ → Prop) (event' : α × τ → Prop)
    (hevent : ∀ (value : α) (state : σ) (state' : τ), rel state state' → ¬ bad state →
      (event (value, state) ↔ event' (value, state')))
    (computation : OracleComp spec α) :
    ∀ (state : σ) (state' : τ), rel state state' →
      Pr[fun result : α × σ => event result ∧ ¬ bad result.2 |
          (simulateQ left computation).run state] =
        Pr[fun result : α × τ => event' result ∧ ¬ bad' result.2 |
          (simulateQ right computation).run state'] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state state' hrelate
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, probEvent_pure,
      probEvent_pure]
    by_cases hbad : bad state
    · rw [if_neg (fun hboth => hboth.2 hbad),
        if_neg (fun hboth => hboth.2 ((hbadIff state state' hrelate).mp hbad))]
    · have hbad' : ¬ bad' state' := fun hbad' =>
        hbad ((hbadIff state state' hrelate).mpr hbad')
      by_cases hev : event (value, state)
      · rw [if_pos ⟨hev, hbad⟩,
          if_pos ⟨(hevent value state state' hrelate hbad).mp hev, hbad'⟩]
      · rw [if_neg (fun hboth => hev hboth.1),
          if_neg (fun hboth => hev ((hevent value state state' hrelate hbad).mpr hboth.1))]
  | query_bind queried next ih =>
    intro state state' hrelate
    by_cases hbad : bad state
    · rw [prob_event_zero left bad hleftSticky event _ state hbad,
        prob_event_zero right bad' hrightSticky event' _ state'
          ((hbadIff state state' hrelate).mp hbad)]
    · rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind]
      rcases hstep queried state state' hrelate hbad with ⟨hleftFlag, hrightFlag⟩ | ⟨hlaw, hcarry⟩
      · rw [prob_event_zero_of_step left bad hleftSticky queried state hleftFlag event next,
          prob_event_zero_of_step right bad' hrightSticky queried state' hrightFlag event' next]
      · rw [probEvent_congr' (fun _ _ => Iff.rfl)
            (evalDist_bind_congr hlaw
              (fun step => (simulateQ right (next step.1)).run step.2)),
          bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        refine tsum_congr fun step => ?_
        by_cases hmem : step ∈ support ((left queried).run state)
        · exact congrArg _ (ih step.1 step.2 _ (hcarry step hmem))
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

end SlhDsaSecurity.HandlerEvent

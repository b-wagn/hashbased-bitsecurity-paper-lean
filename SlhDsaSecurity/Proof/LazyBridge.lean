import SlhDsaSecurity.Proof.SensitiveQuery

/-!
# A lazy presentation and an eager one flag the same event as often

`SensitiveQuery.prob_probes_sensitive_le` charges the input half's event at `2 ^ -128` per
query for a run that does not consult the cell table, the table being drawn afterwards. What a
game offers is a run against a cache *programmed* from that table. This file is the bridge:
two presentations of the same run that agree except where the event has already fired assign
that event exactly the same probability.

The bridge is not a cache comparison. `BlindComparison.prob_touched_eq` compares two caches
agreeing off a set of inputs **fixed before the run**, and the set here is not fixed: it is the
canonical inputs of the nodes that are sensitive *now*, and it shrinks as signatures release
cells. `AgreeOff` is not preserved across a release, so that lemma does not apply.

Nor is it VCVio's `QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad`. That
bounds the *advantage* of distinguishing the two games by `expectedQuerySlack + Pr[bad]`, which
is a bound with a per-query slack, and the input half has no room for one — it is
`q / 2 ^ 128` exactly. Its hypotheses also compare the two handlers at a **shared** state
(`h_step_eq_uncharged` asks for `(h₀ t).run p = (h₁ t).run p` at every `p`), while a lazy
presentation and an eager one have related states, not equal ones: the eager state carries the
whole table and the lazy state only the part that has been drawn.

What is true, and what is proved here, is an equality rather than a bound. Let `refine` send a
lazy state to the distribution of its eager presentations — in the game, "draw the cells that
are still undetermined". Then:

* a query that is bad at a lazy state is bad at every eager presentation of it, and sets the
  flag on both sides, so the event is decided before the two can diverge;
* a query that is not bad **commutes** with `refine`: drawing the remaining cells and then
  answering has the same law as answering and then drawing the remaining cells. This is the
  deferred-sampling move `CanonicalGraph.Programming.warmup_seed_uniform` already makes for the
  walk, one step at a time.

`probEvent_flag_refine_eq` is the conclusion: the eager run and the lazy run flag the event
with the same probability, with no slack. Only the commutation is a real obligation;
everything else is bookkeeping about a sticky flag.

**What it reaches and what it does not.** `Bad` is a predicate on the state and the query, and
`hbadRefine` asks it to be the same at a lazy state and at every eager presentation of it. A
lazy presentation that *defers* the staked cells does not satisfy that, and the failure is
exactly locatable: at a query naming a node whose staked cell is still undrawn, the lazy state
has no sensitivity to report, while the presentation that drew that cell to the matching value
does. So the sensitive-query event of `SensitiveQuery` — which is decided only once the
deferred table is drawn — is not a `Bad` in this sense, and the bridge does not by itself carry
`prob_probes_sensitive_le` to a programmed cache.

A lazy handler that draws the staked cell *at the probe* rather than deferring it does satisfy
the commutation at every query, `Bad` becoming vacuous: drawing a cell at the probe and drawing
it in the final batch are the same law. The charge then has to be re-proved against a partly
drawn table, where a repeated probe at a node whose cell was drawn at an earlier probe is
conditioned on that earlier probe having missed. That is an additive cost, not a per-query one,
but it is not `prob_record_sensitive_le`, which is stated for a table drawn entirely after the
run.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.LazyBridge

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Binding a common continuation after two computations of the same law gives the same law. -/
theorem evalDist_bind_congr_right {α β : Type} {oa ob : ProbComp α} (hlaw : 𝒟[oa] = 𝒟[ob])
    (k : α → ProbComp β) : 𝒟[oa >>= k] = 𝒟[ob >>= k] := by
  rw [evalDist_bind, evalDist_bind, hlaw]

/-! ## A sticky flag is already certain

Once the flag is set, the event is decided: whatever the run does afterwards, it ends flagged.
This is what makes the divergence at a bad query free. -/

/-- **A flagged run ends flagged.** -/
theorem flag_one {γ : Type} (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (impl t).run p] = 0)
    (hsticky : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((impl t).run (s, true)), z.2.2 = true)
    (oa : OracleComp spec γ) (s : σ) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
      (simulateQ impl oa).run (s, true)] = 1 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, probEvent_pure]
    simp
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probEvent_bind_eq_tsum]
    calc ∑' p, Pr[= p | (impl t).run (s, true)] *
          Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
            (simulateQ impl (next p.1)).run p.2]
        = ∑' p, Pr[= p | (impl t).run (s, true)] := by
          refine tsum_congr fun p => ?_
          by_cases hmem : p ∈ support ((impl t).run (s, true))
          · have hflag : p.2.2 = true := hsticky t s p hmem
            rw [show p.2 = (p.2.1, true) from by rw [← hflag], ih p.1 p.2.1, mul_one]
          · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
      _ = 1 := by
          have hmass := probFailure_add_tsum_probOutput ((impl t).run (s, true))
          rw [hfail t (s, true), zero_add] at hmass
          exact hmass

/-- **A bad query is already certain.** Whatever the state, a query that is bad there sets the
flag, and a flagged run ends flagged. -/
theorem bad_one {γ : Type} (impl : QueryImpl spec (StateT (σ × Bool) ProbComp))
    (Bad : σ → spec.Domain → Prop)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (impl t).run p] = 0)
    (hsticky : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((impl t).run (s, true)), z.2.2 = true)
    (hfires : ∀ (t : spec.Domain) (s : σ) (flag : Bool), Bad s t →
      ∀ z ∈ support ((impl t).run (s, flag)), z.2.2 = true)
    (t : spec.Domain) (next : spec.Range t → OracleComp spec γ) (s : σ) (flag : Bool)
    (hbad : Bad s t) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
      (impl t).run (s, flag) >>= fun p => (simulateQ impl (next p.1)).run p.2] = 1 := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' p, Pr[= p | (impl t).run (s, flag)] *
        Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
          (simulateQ impl (next p.1)).run p.2]
      = ∑' p, Pr[= p | (impl t).run (s, flag)] := by
        refine tsum_congr fun p => ?_
        by_cases hmem : p ∈ support ((impl t).run (s, flag))
        · have hflag : p.2.2 = true := hfires t s flag hbad p hmem
          rw [show p.2 = (p.2.1, true) from by rw [← hflag],
            flag_one impl hfail hsticky (next p.1) p.2.1, mul_one]
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
    _ = 1 := by
        have hmass := probFailure_add_tsum_probOutput ((impl t).run (s, flag))
        rw [hfail t (s, flag), zero_add] at hmass
        exact hmass


/-! ## Two handlers that agree until the flag fires

The refinement above compares one handler with itself. Two *different* handlers that agree
except where the flag fires assign it the same probability for the same reason, and that is the
comparison a lazy presentation needs against an eager one when both draw their randomness up
front, so there is nothing for a refinement to draw.

The comparison has to be made once, for the whole event. Stalling it at one coordinate would be
unsound: handlers that differ at the inputs the flag fires on differ at *all* of them, so two
runs stalled at one coordinate can still diverge earlier at another, and "they agree while
unfrozen" would be false rather than merely weak.

Note where the flag lives. It is in the comparison only; nothing here reads it, and in
particular the handler that answers from a table never needs to. -/

/-- **Two handlers agreeing off the flag's trigger flag it equally often.** -/
theorem probEvent_flag_two_handlers_eq {γ : Type}
    (left right : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Bad : σ → spec.Domain → Prop)
    (hfailLeft : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (left t).run p] = 0)
    (hfailRight : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (right t).run p] = 0)
    (hstickyLeft : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((left t).run (s, true)), z.2.2 = true)
    (hstickyRight : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((right t).run (s, true)), z.2.2 = true)
    (hfiresLeft : ∀ (t : spec.Domain) (s : σ) (flag : Bool), Bad s t →
      ∀ z ∈ support ((left t).run (s, flag)), z.2.2 = true)
    (hfiresRight : ∀ (t : spec.Domain) (s : σ) (flag : Bool), Bad s t →
      ∀ z ∈ support ((right t).run (s, flag)), z.2.2 = true)
    (hagree : ∀ (t : spec.Domain) (p : σ × Bool), ¬ Bad p.1 t →
      𝒟[(left t).run p] = 𝒟[(right t).run p])
    (oa : OracleComp spec γ) (p : σ × Bool) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true | (simulateQ left oa).run p] =
      Pr[fun z : γ × (σ × Bool) => z.2.2 = true | (simulateQ right oa).run p] := by
  classical
  induction oa using OracleComp.inductionOn generalizing p with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases hp : Bad p.1 t
    · rw [bad_one left Bad hfailLeft hstickyLeft hfiresLeft t next p.1 p.2 hp,
        bad_one right Bad hfailRight hstickyRight hfiresRight t next p.1 p.2 hp]
    · rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine tsum_congr fun step => ?_
      rw [probOutput_congr rfl (hagree t p hp), ih step.1 step.2]

/-! ## The bridge

`refine s` is the distribution of eager presentations of the lazy state `s` — in the game, the
cells still undetermined, drawn now rather than on demand. The two hypotheses that carry
content are that badness does not depend on which presentation was drawn, and that a non-bad
step commutes with drawing them. -/

/-- **The lazy run and its eager presentation flag the event equally often.** -/
theorem probEvent_flag_refine_eq {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Bad : σ → spec.Domain → Prop)
    (refine : σ → ProbComp σ)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (impl t).run p] = 0)
    (hsticky : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((impl t).run (s, true)), z.2.2 = true)
    (hfires : ∀ (t : spec.Domain) (s : σ) (flag : Bool), Bad s t →
      ∀ z ∈ support ((impl t).run (s, flag)), z.2.2 = true)
    (hrefineMass : ∀ s : σ, Pr[⊥ | refine s] = 0)
    (hbadRefine : ∀ (t : spec.Domain) (s : σ), ∀ s' ∈ support (refine s), Bad s' t ↔ Bad s t)
    (hcommute : ∀ (t : spec.Domain) (s : σ) (flag : Bool), ¬ Bad s t →
      𝒟[refine s >>= fun s' => (impl t).run (s', flag)] =
        𝒟[(impl t).run (s, flag) >>= fun p =>
            (fun eager => (p.1, (eager, p.2.2))) <$> refine p.2.1])
    (oa : OracleComp spec γ) (s : σ) (flag : Bool) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
        refine s >>= fun s' => (simulateQ impl oa).run (s', flag)] =
      Pr[fun z : γ × (σ × Bool) => z.2.2 = true | (simulateQ impl oa).run (s, flag)] := by
  induction oa using OracleComp.inductionOn generalizing s flag with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    have hinner : ∀ state : σ,
        Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
          (pure (value, (state, flag)) : ProbComp (γ × (σ × Bool)))] =
        (if flag = true then 1 else 0) := by
      intro state
      rw [probEvent_pure]
    rw [probEvent_bind_eq_tsum, hinner s]
    simp only [hinner]
    rw [ENNReal.tsum_mul_right]
    have hmass := probFailure_add_tsum_probOutput (refine s)
    rw [hrefineMass s, zero_add] at hmass
    rw [hmass, one_mul]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases hbad : Bad s t
    · -- The event is decided here, whichever presentation is in play.
      rw [bad_one impl Bad hfail hsticky hfires t next s flag hbad, probEvent_bind_eq_tsum]
      calc ∑' s', Pr[= s' | refine s] *
            Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
              (impl t).run (s', flag) >>= fun p => (simulateQ impl (next p.1)).run p.2]
          = ∑' s', Pr[= s' | refine s] := by
            refine tsum_congr fun s' => ?_
            by_cases hmem : s' ∈ support (refine s)
            · rw [bad_one impl Bad hfail hsticky hfires t next s' flag
                ((hbadRefine t s s' hmem).mpr hbad), mul_one]
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
        _ = 1 := by
            have hmass := probFailure_add_tsum_probOutput (refine s)
            rw [hrefineMass s, zero_add] at hmass
            exact hmass
    · -- The step commutes with drawing the remaining cells, and the recursion closes it.
      have hstep := evalDist_bind_congr_right (hcommute t s flag hbad)
        (fun p => (simulateQ impl (next p.1)).run p.2)
      rw [← bind_assoc, probEvent_congr' (fun _ _ => Iff.rfl) hstep, bind_assoc]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine tsum_congr fun p => congrArg _ ?_
      rw [bind_map_left]
      exact ih p.1 p.2.1 p.2.2


/-- **The bridge when no step is excepted.** If every step commutes with drawing the remaining
randomness, the two presentations agree on the flag outright. This is the form a lazy handler
that draws a cell *at the probe* takes rather than deferring it: drawing it there and drawing
it in the final batch are the same law, so there is no step to except. -/
theorem probEvent_flag_refine_eq_of_commute {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (refine : σ → ProbComp σ)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (impl t).run p] = 0)
    (hsticky : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((impl t).run (s, true)), z.2.2 = true)
    (hrefineMass : ∀ s : σ, Pr[⊥ | refine s] = 0)
    (hcommute : ∀ (t : spec.Domain) (s : σ) (flag : Bool),
      𝒟[refine s >>= fun s' => (impl t).run (s', flag)] =
        𝒟[(impl t).run (s, flag) >>= fun p =>
            (fun eager => (p.1, (eager, p.2.2))) <$> refine p.2.1])
    (oa : OracleComp spec γ) (s : σ) (flag : Bool) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
        refine s >>= fun s' => (simulateQ impl oa).run (s', flag)] =
      Pr[fun z : γ × (σ × Bool) => z.2.2 = true | (simulateQ impl oa).run (s, flag)] :=
  probEvent_flag_refine_eq impl (fun _ _ => False) refine hfail hsticky
    (fun _ _ _ hbad => absurd hbad not_false) hrefineMass (fun _ _ _ _ => Iff.rfl)
    (fun t s flag _ => hcommute t s flag) oa s flag

/-- **The bound transfers.** A bound on the lazy presentation is a bound on the eager one, with
nothing added. -/
theorem probEvent_flag_refine_le {γ : Type}
    (impl : QueryImpl spec (StateT (σ × Bool) ProbComp)) (Bad : σ → spec.Domain → Prop)
    (refine : σ → ProbComp σ)
    (hfail : ∀ (t : spec.Domain) (p : σ × Bool), Pr[⊥ | (impl t).run p] = 0)
    (hsticky : ∀ (t : spec.Domain) (s : σ),
      ∀ z ∈ support ((impl t).run (s, true)), z.2.2 = true)
    (hfires : ∀ (t : spec.Domain) (s : σ) (flag : Bool), Bad s t →
      ∀ z ∈ support ((impl t).run (s, flag)), z.2.2 = true)
    (hrefineMass : ∀ s : σ, Pr[⊥ | refine s] = 0)
    (hbadRefine : ∀ (t : spec.Domain) (s : σ), ∀ s' ∈ support (refine s), Bad s' t ↔ Bad s t)
    (hcommute : ∀ (t : spec.Domain) (s : σ) (flag : Bool), ¬ Bad s t →
      𝒟[refine s >>= fun s' => (impl t).run (s', flag)] =
        𝒟[(impl t).run (s, flag) >>= fun p =>
            (fun eager => (p.1, (eager, p.2.2))) <$> refine p.2.1])
    (oa : OracleComp spec γ) (s : σ) (flag : Bool) (bound : ℝ≥0∞)
    (hlazy : Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
      (simulateQ impl oa).run (s, flag)] ≤ bound) :
    Pr[fun z : γ × (σ × Bool) => z.2.2 = true |
      refine s >>= fun s' => (simulateQ impl oa).run (s', flag)] ≤ bound :=
  le_of_eq_of_le (probEvent_flag_refine_eq impl Bad refine hfail hsticky hfires
    hrefineMass hbadRefine hcommute oa s flag) hlazy

end SlhDsaSecurity.LazyBridge

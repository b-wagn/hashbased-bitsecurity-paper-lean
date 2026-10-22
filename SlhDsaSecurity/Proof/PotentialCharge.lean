import SlhDsaSecurity.Proof.ClassExpectation

/-!
# A charge whose payment comes from earlier queries

`ClassExpectation.prob_bad_le_expected_cost` pays for a bad answer out of the cost of the very
query that drew it, and concludes at the final cache. Two things it cannot do, and the
development has now wanted both:

* an event whose chance at one query is set by what *earlier* queries put in the cache — the
  units that pay for it were charged before the step that can go wrong;
* an event that is not a property of the final cache at all, because it is an ordering: the
  cache cannot say which of two of its entries was installed first.

This file is the charge for both. The run carries whatever bookkeeping the event needs in its
own state, and the state carries two numbers: a **gauge**, which only grows and is what the
bound is finally read at, and a **potential**, which the gauge's growth pays into and the event
spends. The conclusion is the potential standing at the start plus the expected growth of the
gauge, so a query may be paid for long after the unit that pays for it was charged.

`prob_bad_le_expected_cost` is the case `potential = 0` with the gauge counting the in-class
queries, where the step hypothesis reduces to `rate ≤ 1 * rate`.

**What the step hypothesis says, and why it is shaped that way.** At a fresh query it asks for
two numbers that do not depend on the answer about to be drawn: a bound on the potential after
the step, and the gauge after the step. The chance of the event firing now, plus the potential
left standing, must be covered by the potential standing before plus the gauge's increase. The
answer-independence is the whole reason the induction closes — the tail's bound has to be
pulled out of an expectation over an answer those two numbers must not see — and asking for
them as numbers is asking for that property exactly where it is used. A potential and a gauge
that read only which inputs the state holds, and not what it holds at them, always supply
them.

**The oracle is a parameter**, described by its three steps: a private coin leaves the state
alone, a cached query answers from the state and leaves it alone, and a fresh query draws
uniformly and takes the state wherever `stepOf` says. Every recording oracle in this
development is of that shape, which is what makes the charge reusable rather than another
bespoke induction.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.PotentialCharge

open Security ClassExpectation

variable {σ : Type}

/-! ## Two readings of an expectation -/

/-- An expectation reads its count only on the support. -/
theorem expected_congr_support {β : Type} (run : ProbComp β) (count other : β → Nat)
    (hagree : ∀ value ∈ support run, count value = other value) :
    expected run count = expected run other := by
  refine tsum_congr fun value => ?_
  by_cases hmem : value ∈ support run
  · rw [hagree value hmem]
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-- A constant inside an average is the constant. -/
theorem tsum_const_add {β : Type} (run : ProbComp β) (hmass : Pr[⊥ | run] = 0) (constant : ℝ≥0∞)
    (value : β → ℝ≥0∞) :
    ∑' x : β, Pr[= x | run] * (constant + value x) =
      constant + ∑' x : β, Pr[= x | run] * value x := by
  calc ∑' x : β, Pr[= x | run] * (constant + value x)
      = ∑' x : β, (Pr[= x | run] * constant + Pr[= x | run] * value x) :=
        tsum_congr fun x => mul_add _ _ _
    _ = (∑' x : β, Pr[= x | run] * constant) + ∑' x : β, Pr[= x | run] * value x :=
        ENNReal.tsum_add
    _ = constant + ∑' x : β, Pr[= x | run] * value x := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hmass, one_mul]

/-! ## The charge -/

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The potential charge, with a continuation.** The same bound for a run followed by anything,
and what is asked of the continuation is **the conclusion's own shape at the continuation's own
starting state**: its potential, its gauge, its own offsets.

That is the decision that makes the charge compose, and it is not recoverable afterwards. A
three-stage bracketed run cannot be one `simulateQ` of one computation, so the stages have to be
composed; and a later stage's probability depends on the state an earlier one left. Stated this
way each layer quotes only its own offsets, so nothing has to relate a later stage's state back
to the first — the telescoping `gauge state ≤ after ≤ gaugeFinal w` happens inside one layer.

`prob_fired_le` is the case `cont := pure`, where the continuation's bound is the old `pure`
case: a run that has not fired cannot have fired. -/
theorem prob_fired_le_cont (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
    (cacheOf : σ → QueryCache HashSpec) (stepOf : σ → Bytes → HashOutput → σ)
    (noticeOf : σ → Bytes → σ)
    (hinl : ∀ (coin : unifSpec.Domain) (state : σ) (step : OracleWorld.Range (Sum.inl coin) × σ),
      step ∈ support ((oracle (Sum.inl coin)).run state) → step.2 = state)
    (hinlMass : ∀ (coin : unifSpec.Domain) (state : σ),
      Pr[⊥ | (oracle (Sum.inl coin)).run state] = 0)
    (hcached : ∀ (input : Bytes) (state : σ) (answer : HashOutput),
      cacheOf state input = some answer →
        (oracle (Sum.inr input)).run state =
          (pure (answer, noticeOf state input) : ProbComp _))
    (hfresh : ∀ (input : Bytes) (state : σ), cacheOf state input = none →
      (oracle (Sum.inr input)).run state =
        (fun answer => (answer, stepOf state input answer)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput))
    (hmass : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ),
      Pr[⊥ | (simulateQ oracle inner).run state] = 0)
    (fired : σ → Prop) (potential gauge : σ → Nat) (rate : ℝ≥0∞)
    (hnoticeFired : ∀ (state : σ) (input : Bytes), fired (noticeOf state input) → fired state)
    (hnoticePotential : ∀ (state : σ) (input : Bytes),
      potential (noticeOf state input) ≤ potential state)
    (hnoticeGauge : ∀ (state : σ) (input : Bytes), gauge (noticeOf state input) = gauge state)
    (hstepGauge : ∀ (state : σ) (input : Bytes) (answer : HashOutput),
      gauge state ≤ gauge (stepOf state input answer))
    (hgauge : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ)
      (result : β × σ), result ∈ support ((simulateQ oracle inner).run state) →
        gauge state ≤ gauge result.2)
    (hstep : ∀ (state : σ) (input : Bytes), cacheOf state input = none → ¬ fired state →
      ∃ bound after : Nat,
        (∀ answer : HashOutput, ¬ fired (stepOf state input answer) →
            potential (stepOf state input answer) ≤ bound) ∧
          (∀ answer : HashOutput, gauge (stepOf state input answer) = after) ∧
            Pr[fun answer : HashOutput => fired (stepOf state input answer) |
                ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
              ((potential state : Nat) : ℝ≥0∞) * rate +
                ((after - gauge state : Nat) : ℝ≥0∞) * rate)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (cont : α × σ → ProbComp γ) (firedFinal : γ → Prop) (gaugeFinal : γ → Nat)
    (hcontMass : ∀ z : α × σ, Pr[⊥ | cont z] = 0)
    (hcontGauge : ∀ (z : α × σ) (w : γ), w ∈ support (cont z) → gauge z.2 ≤ gaugeFinal w)
    (hcont : ∀ z : α × σ, ¬ fired z.2 →
      Pr[firedFinal | cont z] ≤ ((potential z.2 : Nat) : ℝ≥0∞) * rate +
        expected (cont z) (fun w => gaugeFinal w - gauge z.2) * rate) :
    ∀ state : σ, ¬ fired state →
      Pr[firedFinal | (simulateQ oracle computation).run state >>= cont] ≤
        ((potential state : Nat) : ℝ≥0∞) * rate +
          expected ((simulateQ oracle computation).run state >>= cont)
            (fun w => gaugeFinal w - gauge state) * rate := by
  classical
  have hmassCont : ∀ (inner : OracleComp OracleWorld α) (state : σ),
      Pr[⊥ | (simulateQ oracle inner).run state >>= cont] = 0 := fun inner state =>
    (probFailure_bind_eq_zero_iff _ _).mpr ⟨hmass α inner state, fun z _ => hcontMass z⟩
  have hgaugeCont : ∀ (inner : OracleComp OracleWorld α) (state : σ) (w : γ),
      w ∈ support ((simulateQ oracle inner).run state >>= cont) → gauge state ≤ gaugeFinal w := by
    intro inner state w hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hwz⟩ := hw
    exact le_trans (hgauge α inner state z hz) (hcontGauge z w hwz)
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hstate
    rw [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hcont (value, state) hstate
  | query_bind queried next ih =>
    intro state hstate
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with coin | input
    · rw [probEvent_bind_eq_tsum, expected_bind]
      calc ∑' step : OracleWorld.Range (Sum.inl coin) × σ,
            Pr[= step | (oracle (Sum.inl coin)).run state] *
              Pr[firedFinal | (simulateQ oracle (next step.1)).run step.2 >>= cont]
          ≤ ∑' step : OracleWorld.Range (Sum.inl coin) × σ,
              Pr[= step | (oracle (Sum.inl coin)).run state] *
                (((potential state : Nat) : ℝ≥0∞) * rate +
                  expected ((simulateQ oracle (next step.1)).run step.2 >>= cont)
                    (fun w => gaugeFinal w - gauge state) * rate) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((oracle (Sum.inl coin)).run state)
            · refine mul_le_mul' le_rfl ?_
              have hsame : step.2 = state := hinl coin state step hmem
              rw [hsame]
              exact ih step.1 state hstate
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
        _ = ((potential state : Nat) : ℝ≥0∞) * rate +
              ∑' step : OracleWorld.Range (Sum.inl coin) × σ,
                Pr[= step | (oracle (Sum.inl coin)).run state] *
                  (expected ((simulateQ oracle (next step.1)).run step.2 >>= cont)
                    (fun w => gaugeFinal w - gauge state) * rate) :=
            tsum_const_add ((oracle (Sum.inl coin)).run state) (hinlMass coin state) _ _
        _ = _ := by
            rw [← ENNReal.tsum_mul_right]
            exact congrArg _ (tsum_congr fun step => (mul_assoc _ _ _).symm)
    · cases hcache : cacheOf state input with
      | some answer =>
        rw [hcached input state answer hcache]
        show Pr[firedFinal |
            (simulateQ oracle (next answer)).run (noticeOf state input) >>= cont] ≤
          ((potential state : Nat) : ℝ≥0∞) * rate +
            expected ((simulateQ oracle (next answer)).run (noticeOf state input) >>= cont)
              (fun w => gaugeFinal w - gauge state) * rate
        refine le_trans (ih answer (noticeOf state input)
          (fun hfired => hstate (hnoticeFired state input hfired))) ?_
        rw [hnoticeGauge state input]
        exact add_le_add (mul_le_mul' (Nat.cast_le.mpr (hnoticePotential state input)) le_rfl)
          le_rfl
      | none =>
        obtain ⟨bound, after, hbound, hafter, hpay⟩ := hstep state input hcache hstate
        rw [hfresh input state hcache]
        show Pr[firedFinal |
            ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
              ((simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont)] ≤
          ((potential state : Nat) : ℝ≥0∞) * rate +
            expected (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
              ((simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont))
              (fun w => gaugeFinal w - gauge state) * rate
        rw [probEvent_bind_eq_tsum, expected_bind]
        have hsplit : ∀ answer : HashOutput,
            expected ((simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont)
                (fun w => gaugeFinal w - gauge state) =
              ((after - gauge state : Nat) : ℝ≥0∞) +
                expected ((simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont)
                  (fun w => gaugeFinal w - after) := by
          intro answer
          rw [expected_congr_support
            ((simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont)
            (fun w => gaugeFinal w - gauge state)
            (fun w => (after - gauge state) + (gaugeFinal w - after)) ?_]
          · exact expected_const_add _ (hmassCont _ _) _ _
          · intro w hw
            have hlower : gauge state ≤ after := by
              rw [← hafter answer]
              exact hstepGauge state input answer
            have hupper : after ≤ gaugeFinal w := by
              rw [← hafter answer]
              exact hgaugeCont (next answer) (stepOf state input answer) w hw
            omega
        simp only [hsplit]
        rw [tsum_const_add ($ᵗ HashOutput : ProbComp HashOutput) (by simp) _ _]
        have hpointwise : ∀ answer : HashOutput,
            Pr[firedFinal |
                (simulateQ oracle (next answer)).run (stepOf state input answer) >>= cont] ≤
              (if fired (stepOf state input answer) then 1 else 0) +
                (((bound : Nat) : ℝ≥0∞) * rate +
                  expected ((simulateQ oracle (next answer)).run (stepOf state input answer)
                      >>= cont)
                    (fun w => gaugeFinal w - after) * rate) := by
          intro answer
          by_cases hfired : fired (stepOf state input answer)
          · rw [if_pos hfired]
            exact le_add_right probEvent_le_one
          · rw [if_neg hfired, zero_add]
            refine le_trans (ih answer (stepOf state input answer) hfired) ?_
            rw [hafter answer]
            exact add_le_add (mul_le_mul' (by exact_mod_cast hbound answer hfired) le_rfl) le_rfl
        refine le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (hpointwise answer)) ?_
        rw [show (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                ((if fired (stepOf state input answer) then 1 else 0) +
                  (((bound : Nat) : ℝ≥0∞) * rate +
                    expected ((simulateQ oracle (next answer)).run (stepOf state input answer)
                        >>= cont)
                      (fun w => gaugeFinal w - after) * rate))) =
              (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (if fired (stepOf state input answer) then 1 else 0)) +
                ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (((bound : Nat) : ℝ≥0∞) * rate +
                    expected ((simulateQ oracle (next answer)).run (stepOf state input answer)
                        >>= cont)
                      (fun w => gaugeFinal w - after) * rate) from by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun answer => mul_add _ _ _]
        rw [tsum_const_add ($ᵗ HashOutput : ProbComp HashOutput) (by simp) _ _,
          show (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if fired (stepOf state input answer) then 1 else 0)) =
              ∑' answer : HashOutput,
                (if fired (stepOf state input answer) then
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) from
            tsum_congr fun answer => by
              by_cases hfired : fired (stepOf state input answer) <;> simp [hfired],
          ← probEvent_eq_tsum_ite, ← add_assoc, add_mul, ← ENNReal.tsum_mul_right]
        refine le_trans (add_le_add hpay
          (le_of_eq (tsum_congr fun answer => (mul_assoc _ _ _).symm))) ?_
        exact le_of_eq (add_assoc _ _ _)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The potential charge.** A run ends in a fired state with probability at most the potential
it started with, plus the expected growth of its gauge, both at the rate — provided each fresh
query pays for its own chance of firing out of the potential it leaves behind and the gauge's
own increase.

The event may be any property of the run's final state, so it may be an ordering the cache
cannot express; the payment may come from queries made long before the one that fires.

**A step that notices.** `hcached` once said a cache hit leaves the state alone. A view that
records something about every query — that the signer was serving it, say — does not: it files
on a hit as much as on a miss. So a hit takes the state to `noticeOf state input`, and the
charge asks three things of that map and nothing else, all of which hold when the notice writes
a component the firing predicate, the potential and the gauge do not read.

That last clause is a constraint on the instantiation and not a formality. A firing predicate
that *does* read what the notice writes can be fired by a hit, which is a deterministic step,
and a deterministic step cannot be paid for out of `potential * rate`: its probability is one or
zero. So a carrier's firing predicate has to change only where a fresh answer is drawn, which is
where `hstep` lives and where the rate is actually spent. -/
theorem prob_fired_le (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
    (cacheOf : σ → QueryCache HashSpec) (stepOf : σ → Bytes → HashOutput → σ)
    (noticeOf : σ → Bytes → σ)
    (hinl : ∀ (coin : unifSpec.Domain) (state : σ) (step : OracleWorld.Range (Sum.inl coin) × σ),
      step ∈ support ((oracle (Sum.inl coin)).run state) → step.2 = state)
    (hinlMass : ∀ (coin : unifSpec.Domain) (state : σ),
      Pr[⊥ | (oracle (Sum.inl coin)).run state] = 0)
    (hcached : ∀ (input : Bytes) (state : σ) (answer : HashOutput),
      cacheOf state input = some answer →
        (oracle (Sum.inr input)).run state =
          (pure (answer, noticeOf state input) : ProbComp _))
    (hfresh : ∀ (input : Bytes) (state : σ), cacheOf state input = none →
      (oracle (Sum.inr input)).run state =
        (fun answer => (answer, stepOf state input answer)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput))
    (hmass : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ),
      Pr[⊥ | (simulateQ oracle inner).run state] = 0)
    (fired : σ → Prop) (potential gauge : σ → Nat) (rate : ℝ≥0∞)
    (hnoticeFired : ∀ (state : σ) (input : Bytes), fired (noticeOf state input) → fired state)
    (hnoticePotential : ∀ (state : σ) (input : Bytes),
      potential (noticeOf state input) ≤ potential state)
    (hnoticeGauge : ∀ (state : σ) (input : Bytes), gauge (noticeOf state input) = gauge state)
    (hstepGauge : ∀ (state : σ) (input : Bytes) (answer : HashOutput),
      gauge state ≤ gauge (stepOf state input answer))
    (hgauge : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ)
      (result : β × σ), result ∈ support ((simulateQ oracle inner).run state) →
        gauge state ≤ gauge result.2)
    (hstep : ∀ (state : σ) (input : Bytes), cacheOf state input = none → ¬ fired state →
      ∃ bound after : Nat,
        (∀ answer : HashOutput, ¬ fired (stepOf state input answer) →
            potential (stepOf state input answer) ≤ bound) ∧
          (∀ answer : HashOutput, gauge (stepOf state input answer) = after) ∧
            Pr[fun answer : HashOutput => fired (stepOf state input answer) |
                ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
              ((potential state : Nat) : ℝ≥0∞) * rate +
                ((after - gauge state : Nat) : ℝ≥0∞) * rate)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : σ, ¬ fired state →
      Pr[fun result : α × σ => fired result.2 |
          (simulateQ oracle computation).run state] ≤
        ((potential state : Nat) : ℝ≥0∞) * rate +
          expected ((simulateQ oracle computation).run state)
            (fun result => gauge result.2 - gauge state) * rate := by
  classical
  intro state hstate
  have hmain := prob_fired_le_cont oracle cacheOf stepOf noticeOf hinl hinlMass hcached hfresh
    hmass fired potential gauge rate hnoticeFired hnoticePotential hnoticeGauge hstepGauge
    hgauge hstep computation (fun z => (pure z : ProbComp (α × σ)))
    (fun result => fired result.2) (fun result => gauge result.2)
    (fun _ => by simp) (fun _ _ hw => by
      rw [support_pure, Set.mem_singleton_iff] at hw
      rw [hw])
    (fun z hz => by
      refine le_of_eq_of_le (b := 0) ?_ (by simp)
      exact probEvent_eq_zero fun result hresult hfired => by
        rw [support_pure, Set.mem_singleton_iff] at hresult
        exact hz (hresult ▸ hfired))
    state hstate
  rw [bind_pure] at hmain
  exact hmain

end SlhDsaSecurity.PotentialCharge

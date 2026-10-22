import SlhDsaSecurity.Proof.PotentialCharge
import SlhDsaSecurity.Proof.PhaseFusion

/-!
# The potential charge across a bracketed phase, and across three stages

`PotentialCharge.prob_fired_le_cont` charges a run of one handler over `OracleWorld` followed by
anything. This file carries it to the two shapes a bracketed game is made of: the adversary's
phase under `PhaseFusion.fuseServing`, and the three stages of
`BracketedRun.IsBracketedRecorderRun`.

**There is no second induction over `OracleWorld` here.** `PhaseFusion.fuse` runs
`simulateQ outer` on *both* branches — the inner handler lifts a query, world or signing, into
an `OracleComp OracleWorld` and the outer handler simulates it — so every case of the induction
below is one nested run followed by the rest of the phase. The nested run is discharged by the
continuation form, and that lemma's hypothesis about its continuation is this induction's own
hypothesis at the tail.

**What the brackets have to be.** The opening bracket runs before the sub-run and the closing
one after it, and the charge reads three things of a state: whether it has fired, its potential,
and its gauge. So a bracket has to leave all three alone — not fire, not raise the potential,
not move the gauge. `Neutral` is that, and it is what `BracketedRun.Bracket` delivers for a
charge whose three readings are functions of the cache and the recordings: the brackets write the
framing and nothing else.

**Each layer quotes only its own offsets.** The three-stage composition relates no stage's state
to any other stage's: stage two's bound is read at the state stage one left, stage three's at the
state stage two left, and the telescoping of gauges happens inside one layer of the continuation
form. A lemma relating the last state back to the first would be a sign the shape is wrong, not
a lemma to prove.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.OrderingCompose

open Security ClassExpectation PhaseFusion

variable {σ : Type} {ω : Type} [Monoid ω]

/-! ## The fused handler's two steps, as equations

Both are `rfl`. They are restated here rather than imported so that this file depends on
`PhaseFusion` alone. -/

theorem fuseServing_run_inl (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (world : OracleWorld.Domain)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inl world)).run state =
      (simulateQ outer (((inner (Sum.inl world)).run).run state.2.1)).run state.2.2 >>=
        fun step => (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, step.2)) :
          ProbComp _) := rfl

theorem fuseServing_run_inr (outer : QueryImpl OracleWorld (StateT σ ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (after : σ → σ) (request : Message)
    (state : ω × SigningLog × σ) :
    ((fuseServing outer inner before after) (Sum.inr request)).run state =
      (simulateQ outer (((inner (Sum.inr request)).run).run state.2.1)).run
          (before request state.2.2) >>= fun step =>
        (pure (step.1.1.1, (state.1 * step.1.1.2, step.1.2, after step.2)) :
          ProbComp _) := rfl

/-! ## What a bracket has to be -/

/-- **What the charge asks of a bracket**: it cannot fire, cannot raise the potential, and cannot
move the gauge. A charge reading only the cache and the recordings gets all three from
`BracketedRun.Bracket`, since the brackets write the framing alone. -/
def Neutral (fired : σ → Prop) (potential gauge : σ → Nat) (f : σ → σ) : Prop :=
  (∀ state : σ, fired (f state) → fired state) ∧
    (∀ state : σ, potential (f state) ≤ potential state) ∧
      ∀ state : σ, gauge (f state) = gauge state

/-- The identity is neutral, which is the unbracketed phase. -/
theorem neutral_id (fired : σ → Prop) (potential gauge : σ → Nat) :
    Neutral fired potential gauge (fun state => state) :=
  ⟨fun _ h => h, fun _ => le_rfl, fun _ => rfl⟩

/-! ## Two facts the fused phase supplies about itself

The charge's continuation hypotheses are read at the fused run, so the two things the
continuation form asks of *its* continuation — that it never fails and that the gauge does not
shrink — have to hold across a phase as well as across a run. Both are ordinary inductions with
no continuation parameter, and the brackets are invisible to both: the opening and closing maps
leave the gauge where it was by `Neutral`, and neither introduces a way to fail.
-/

/-- **The fused run never fails.** -/
theorem mass_fused (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
    (hmass : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ),
      Pr[⊥ | (simulateQ oracle inner).run state] = 0)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ state : ω × SigningLog × σ,
      Pr[⊥ | (simulateQ (fuseServing oracle inner before afterMap) phase).run state] = 0 := by
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure]
    simp
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (probFailure_bind_eq_zero_iff _ _).mpr ⟨?_, fun step _ => ih step.1 step.2⟩
    rcases queried with world | request
    · rw [fuseServing_run_inl]
      exact (probFailure_bind_eq_zero_iff _ _).mpr ⟨hmass _ _ _, fun _ _ => by simp⟩
    · rw [fuseServing_run_inr]
      exact (probFailure_bind_eq_zero_iff _ _).mpr ⟨hmass _ _ _, fun _ _ => by simp⟩

/-- **And its gauge does not shrink.** -/
theorem gauge_fused (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
    (fired : σ → Prop) (potential gauge : σ → Nat)
    (hgauge : ∀ (β : Type) (inner : OracleComp OracleWorld β) (state : σ)
      (result : β × σ), result ∈ support ((simulateQ oracle inner).run state) →
        gauge state ≤ gauge result.2)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (hbefore : ∀ request : Message, Neutral fired potential gauge (before request))
    (hafterMap : Neutral fired potential gauge afterMap)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : ω × SigningLog × σ) (result : α × (ω × SigningLog × σ)),
      result ∈ support ((simulateQ (fuseServing oracle inner before afterMap) phase).run state) →
        gauge state.2.2 ≤ gauge result.2.2.2 := by
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro state result hresult
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [show result.2.2.2 = state.2.2 from by rw [hresult]]
  | query_bind queried next ih =>
    intro state result hresult
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    refine le_trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with world | request
    · rw [fuseServing_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = z.2 from by rw [hpure]]
      exact hgauge _ _ state.2.2 z hz
    · rw [fuseServing_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨z, hz, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [show step.2.2.2 = afterMap z.2 from by rw [hpure], hafterMap.2.2 z.2,
        ← (hbefore request).2.2 state.2.2]
      exact hgauge _ _ (before request state.2.2) z hz

/-! ## The charge across the bracketed phase -/

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The potential charge at the fused handler, with a continuation.** One induction, every case
one nested run.

The bracketed case needs the opening bracket's neutrality to enter the sub-run and the closing
one's to leave it, and nothing else about either: the sub-run's own bound comes from the
continuation form at the state the opening bracket produced, and the rest of the phase's from
this induction's hypothesis at the state the closing bracket produced. -/
theorem prob_fired_le_fused (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
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
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → σ → σ) (afterMap : σ → σ)
    (hbefore : ∀ request : Message, Neutral fired potential gauge (before request))
    (hafterMap : Neutral fired potential gauge afterMap)
    {α γ : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (cont : α × (ω × SigningLog × σ) → ProbComp γ) (firedFinal : γ → Prop)
    (gaugeFinal : γ → Nat)
    (hcontMass : ∀ z : α × (ω × SigningLog × σ), Pr[⊥ | cont z] = 0)
    (hcontGauge : ∀ (z : α × (ω × SigningLog × σ)) (w : γ),
      w ∈ support (cont z) → gauge z.2.2.2 ≤ gaugeFinal w)
    (hcont : ∀ z : α × (ω × SigningLog × σ), ¬ fired z.2.2.2 →
      Pr[firedFinal | cont z] ≤ ((potential z.2.2.2 : Nat) : ℝ≥0∞) * rate +
        expected (cont z) (fun w => gaugeFinal w - gauge z.2.2.2) * rate) :
    ∀ (accumulated : ω) (log : SigningLog) (state : σ), ¬ fired state →
      Pr[firedFinal |
          (simulateQ (fuseServing oracle inner before afterMap) phase).run
            (accumulated, log, state) >>= cont] ≤
        ((potential state : Nat) : ℝ≥0∞) * rate +
          expected ((simulateQ (fuseServing oracle inner before afterMap) phase).run
              (accumulated, log, state) >>= cont)
            (fun w => gaugeFinal w - gauge state) * rate := by
  classical
  induction phase using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log state hstate
    rw [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hcont (value, (accumulated, log, state)) hstate
  | query_bind queried next ih =>
    intro accumulated log state hstate
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with world | request
    · rw [fuseServing_run_inl]
      simp only [bind_assoc, pure_bind]
      exact PotentialCharge.prob_fired_le_cont oracle cacheOf stepOf noticeOf hinl hinlMass
        hcached hfresh hmass fired potential gauge rate hnoticeFired hnoticePotential
        hnoticeGauge hstepGauge hgauge hstep (((inner (Sum.inl world)).run).run log)
        (fun z => (simulateQ (fuseServing oracle inner before afterMap) (next z.1.1.1)).run
          (accumulated * z.1.1.2, z.1.2, z.2) >>= cont)
        firedFinal gaugeFinal
        (fun z => (probFailure_bind_eq_zero_iff _ _).mpr
          ⟨mass_fused oracle hmass inner before afterMap _ _, fun y _ => hcontMass y⟩)
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨y, hy, hwy⟩ := hw
          exact le_trans (gauge_fused oracle fired potential gauge hgauge inner before afterMap
            hbefore hafterMap _ (accumulated * z.1.1.2, z.1.2, z.2) y hy)
            (hcontGauge y w hwy))
        (fun z hz => ih z.1.1.1 (accumulated * z.1.1.2) z.1.2 z.2 hz)
        state hstate
    · rw [fuseServing_run_inr]
      simp only [bind_assoc, pure_bind]
      refine le_trans (PotentialCharge.prob_fired_le_cont oracle cacheOf stepOf noticeOf hinl
        hinlMass hcached hfresh hmass fired potential gauge rate hnoticeFired hnoticePotential
        hnoticeGauge hstepGauge hgauge hstep (((inner (Sum.inr request)).run).run log)
        (fun z => (simulateQ (fuseServing oracle inner before afterMap) (next z.1.1.1)).run
          (accumulated * z.1.1.2, z.1.2, afterMap z.2) >>= cont)
        firedFinal gaugeFinal
        (fun z => (probFailure_bind_eq_zero_iff _ _).mpr
          ⟨mass_fused oracle hmass inner before afterMap _ _, fun y _ => hcontMass y⟩)
        (fun z w hw => by
          rw [mem_support_bind_iff] at hw
          obtain ⟨y, hy, hwy⟩ := hw
          refine le_trans (le_of_eq (hafterMap.2.2 z.2).symm) ?_
          exact le_trans (gauge_fused oracle fired potential gauge hgauge inner before afterMap
            hbefore hafterMap _ (accumulated * z.1.1.2, z.1.2, afterMap z.2) y hy)
            (hcontGauge y w hwy))
        (fun z hz => by
          refine le_trans (ih z.1.1.1 (accumulated * z.1.1.2) z.1.2 (afterMap z.2)
            (fun hfired => hz (hafterMap.1 z.2 hfired))) ?_
          rw [hafterMap.2.2 z.2]
          exact add_le_add (mul_le_mul' (Nat.cast_le.mpr (hafterMap.2.1 z.2)) le_rfl) le_rfl)
        (before request state) (fun hfired => hstate ((hbefore request).1 state hfired))) ?_
      rw [(hbefore request).2.2 state]
      exact add_le_add
        (mul_le_mul' (Nat.cast_le.mpr ((hbefore request).2.1 state)) le_rfl) le_rfl

/-! ## The three stages

`BracketedRun.IsBracketedRecorderRun`'s shape: key generation under the handler, the adversary's
phase fused and bracketed, verification under the handler again, and a `pure` reading the value
off. Three nested applications and no induction — each stage's continuation is the next stage,
and each stage's charge supplies the hypothesis the previous one asked for.

**Nothing here relates the last state to the first.** Stage two's bound is read at the state
stage one left and stage three's at the state stage two left; the gauge telescopes inside one
layer of the continuation form. The only facts crossing a stage boundary are the two the phase
proves about itself.
-/

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **The potential charge across a three-stage bracketed run.** -/
theorem prob_fired_le_threeStage (oracle : QueryImpl OracleWorld (StateT σ ProbComp))
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
    (before : Message → σ → σ) (afterMap : σ → σ)
    (hbefore : ∀ request : Message, Neutral fired potential gauge (before request))
    (hafterMap : Neutral fired potential gauge afterMap)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (outcome : β → α → ω → SigningLog → γ → σ → δ)
    (firedFinal : δ → Prop) (gaugeFinal : δ → Nat)
    (hfiredFinal : ∀ (keys : β) (middle : α) (accumulated : ω) (log : SigningLog) (final : γ)
      (state : σ), firedFinal (outcome keys middle accumulated log final state) → fired state)
    (hgaugeFinal : ∀ (keys : β) (middle : α) (accumulated : ω) (log : SigningLog) (final : γ)
      (state : σ), gauge state ≤ gaugeFinal (outcome keys middle accumulated log final state))
    (start : σ) (hstart : ¬ fired start) :
    Pr[firedFinal |
        (simulateQ oracle first).run start >>= fun keys =>
          (simulateQ (fuseServing oracle (inner keys.1) before afterMap) (phase keys.1)).run
              ((1 : ω), [], keys.2) >>= fun middle =>
            (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
              (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                ProbComp δ)] ≤
      ((potential start : Nat) : ℝ≥0∞) * rate +
        expected ((simulateQ oracle first).run start >>= fun keys =>
            (simulateQ (fuseServing oracle (inner keys.1) before afterMap) (phase keys.1)).run
                ((1 : ω), [], keys.2) >>= fun middle =>
              (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
                (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                  ProbComp δ))
          (fun w => gaugeFinal w - gauge start) * rate := by
  classical
  -- The third stage, and the `pure` that reads the value off.
  have hthird : ∀ (keys : β × σ) (middle : α × (ω × SigningLog × σ)), ¬ fired middle.2.2.2 →
      Pr[firedFinal | (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>=
          fun final => (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
            ProbComp δ)] ≤
        ((potential middle.2.2.2 : Nat) : ℝ≥0∞) * rate +
          expected ((simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>=
              fun final => (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1
                final.2) : ProbComp δ))
            (fun w => gaugeFinal w - gauge middle.2.2.2) * rate := by
    intro keys middle hmiddle
    exact PotentialCharge.prob_fired_le_cont oracle cacheOf stepOf noticeOf hinl hinlMass hcached
      hfresh hmass fired potential gauge rate hnoticeFired hnoticePotential hnoticeGauge
      hstepGauge hgauge hstep (last keys.1 middle.1)
      (fun final => (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
        ProbComp δ))
      firedFinal gaugeFinal (fun _ => by simp)
      (fun z w hw => by
        rw [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact hgaugeFinal _ _ _ _ _ _)
      (fun z hz => by
        refine le_of_eq_of_le (b := 0) ?_ (by simp)
        exact probEvent_eq_zero fun w hw hfiredw => by
          rw [support_pure, Set.mem_singleton_iff] at hw
          exact hz (hfiredFinal _ _ _ _ _ _ (hw ▸ hfiredw)))
      middle.2.2.2 hmiddle
  -- The second stage, with the third as its continuation.
  have hsecond : ∀ keys : β × σ, ¬ fired keys.2 →
      Pr[firedFinal |
          (simulateQ (fuseServing oracle (inner keys.1) before afterMap) (phase keys.1)).run
              ((1 : ω), [], keys.2) >>= fun middle =>
            (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
              (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                ProbComp δ)] ≤
        ((potential keys.2 : Nat) : ℝ≥0∞) * rate +
          expected ((simulateQ (fuseServing oracle (inner keys.1) before afterMap)
                (phase keys.1)).run ((1 : ω), [], keys.2) >>= fun middle =>
              (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
                (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                  ProbComp δ))
            (fun w => gaugeFinal w - gauge keys.2) * rate := by
    intro keys hkeys
    exact prob_fired_le_fused oracle cacheOf stepOf noticeOf hinl hinlMass hcached hfresh hmass
      fired potential gauge rate hnoticeFired hnoticePotential hnoticeGauge hstepGauge hgauge
      hstep (inner keys.1) before afterMap hbefore hafterMap (phase keys.1)
      (fun middle => (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
        (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) : ProbComp δ))
      firedFinal gaugeFinal
      (fun z => (probFailure_bind_eq_zero_iff _ _).mpr ⟨hmass _ _ _, fun _ _ => by simp⟩)
      (fun z w hw => by
        rw [mem_support_bind_iff] at hw
        obtain ⟨final, hfinal, hpure⟩ := hw
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure]
        exact le_trans (hgauge _ _ z.2.2.2 final hfinal) (hgaugeFinal _ _ _ _ _ _))
      (fun z hz => hthird keys z hz) (1 : ω) [] keys.2 hkeys
  -- The first stage, with the second as its continuation.
  exact PotentialCharge.prob_fired_le_cont oracle cacheOf stepOf noticeOf hinl hinlMass hcached
    hfresh hmass fired potential gauge rate hnoticeFired hnoticePotential hnoticeGauge hstepGauge
    hgauge hstep first
    (fun keys => (simulateQ (fuseServing oracle (inner keys.1) before afterMap)
        (phase keys.1)).run ((1 : ω), [], keys.2) >>= fun middle =>
      (simulateQ oracle (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
        (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) : ProbComp δ))
    firedFinal gaugeFinal
    (fun z => (probFailure_bind_eq_zero_iff _ _).mpr
      ⟨mass_fused oracle hmass (inner z.1) before afterMap _ _, fun middle _ =>
        (probFailure_bind_eq_zero_iff _ _).mpr ⟨hmass _ _ _, fun _ _ => by simp⟩⟩)
    (fun z w hw => by
      rw [mem_support_bind_iff] at hw
      obtain ⟨middle, hmiddle, hrest⟩ := hw
      rw [mem_support_bind_iff] at hrest
      obtain ⟨final, hfinal, hpure⟩ := hrest
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      refine le_trans (gauge_fused oracle fired potential gauge hgauge (inner z.1) before
        afterMap hbefore hafterMap _ ((1 : ω), [], z.2) middle hmiddle) ?_
      exact le_trans (hgauge _ _ middle.2.2.2 final hfinal) (hgaugeFinal _ _ _ _ _ _))
    (fun z hz => hsecond z hz) start hstart

end SlhDsaSecurity.OrderingCompose

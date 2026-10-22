import SlhDsaSecurity.Proof.BracketedRun
import SlhDsaSecurity.Proof.CarrierFiles
import SlhDsaSecurity.Proof.OrderingCompose

/-!
# The carrier handler, as the potential charge reads it

`PotentialCharge.prob_fired_le` describes its oracle by three step equations: a private coin
leaves the state alone, a cache hit answers from the state and takes it wherever the notice says,
and a miss draws uniformly and takes it wherever the step says. This file is
`CarrierFiles.countedCarrierRecorder` at those three, with the two maps named.

**Two things the counter does and one it does not.** It bumps on a hash query and stands on a
coin, which is why the coin case gives the state back unchanged; and it is in a component the
charge never reads, which is why naming it costs nothing. `OrderingCompose.mass_run` and
`OrderingCompose.gauge_run` then supply the charge's two run-level hypotheses from these three,
so an instantiation owes steps and nothing else.

**The notice is where the repair shows up.** `noticeAt` is not the identity: the serving notice
files on a hit as well as on a miss, so a cache hit moves the carrier. What it does not move is
the cache or either recording — which is exactly the three laws the charge asks of a notice, and
why a firing predicate reading only those is payable.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierCharge

open Security BracketedRun RecorderView CarriedWitness CarrierFiles HandlerCarrier
  ClassExpectation PhaseFusion

variable (pk : PublicKey) {ω : Type} [Monoid ω]

/-! ## The three states a step can leave -/

/-- The cache a counted carrier state holds. -/
def cacheAt (state : CountedState) : QueryCache HashSpec := state.1.cache

/-- Where a cache hit takes the state: the notice files, the counter bumps, the cache stands and
so do both recordings. -/
noncomputable def noticeAt (state : CountedState) (input : Bytes) : CountedState :=
  (servingNotice pk state.1 input, (state.2.1, state.2.2 + 1))

/-- And where a miss takes it: the answer is installed on top of the notice, and whichever
recording the two tests name gains this query's entry. -/
noncomputable def stepAt (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (state : CountedState) (input : Bytes) (answer : HashOutput) : CountedState :=
  (cacheAnswer (servingNotice pk state.1 input) input answer,
    (@appendedOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep input
      (servingNotice pk state.1 input, state.2.1) answer, state.2.2 + 1))

@[simp] theorem cache_noticeAt (state : CountedState) (input : Bytes) :
    (noticeAt pk state input).1.cache = state.1.cache := by
  rw [noticeAt]
  exact cacheOf_servingNotice pk state.1 input

@[simp] theorem records_noticeAt (state : CountedState) (input : Bytes) :
    (noticeAt pk state input).2.1 = state.2.1 := rfl

/-! ## The three step equations -/

/-- **A private coin leaves the state alone**, counter included: a coin costs nothing. -/
theorem run_inl (rightKeep : Bytes → HandlerCarrier.State → Prop) (coin : unifSpec.Domain)
    (state : CountedState)
    (step : OracleWorld.Range (Sum.inl coin) × CountedState)
    (hstep : step ∈ support (((countedCarrierRecorder pk rightKeep) (Sum.inl coin)).run state)) :
    step.2 = state := by
  rw [countedCarrierRecorder, CountedHandler.withCount_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  have hsame : inner.2 = (state.1, state.2.1) :=
    @recorderOf_step_inl HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep
      coin (state.1, state.2.1) inner
      (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk)]; exact hinner)
  have hvalue : step = (inner.1, (inner.2.1, (inner.2.2, state.2.2 + 0))) := hpure
  rw [hvalue]
  show (inner.2.1, (inner.2.2, state.2.2 + 0)) = state
  rw [show inner.2.1 = state.1 from congrArg Prod.fst hsame,
    show inner.2.2 = state.2.1 from congrArg Prod.snd hsame, Nat.add_zero]

/-- **And it never fails.** -/
theorem run_inl_mass (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (coin : unifSpec.Domain) (state : CountedState) :
    Pr[⊥ | ((countedCarrierRecorder pk rightKeep) (Sum.inl coin)).run state] = 0 := by
  rw [countedCarrierRecorder, CountedHandler.withCount_run]
  refine (probFailure_bind_eq_zero_iff _ _).mpr ⟨?_, fun _ _ => by simp⟩
  rw [@noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep coin (state.1, state.2.1),
    @recorderOf_run_inl HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep coin
      (state.1, state.2.1)]
  simp

/-- **A cache hit answers from the state and files the notice.** -/
theorem run_inr_cached (rightKeep : Bytes → HandlerCarrier.State → Prop) (input : Bytes)
    (state : CountedState) (answer : HashOutput)
    (hcached : cacheAt state input = some answer) :
    ((countedCarrierRecorder pk rightKeep) (Sum.inr input)).run state =
      (pure (answer, noticeAt pk state input) : ProbComp _) := by
  classical
  rw [countedCarrierRecorder, CountedHandler.withCount_run,
    @noticingRecorderOf_run_inr_some HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1) answer hcached,
    pure_bind]
  -- The instance has to be named: the goal's `appendedOf` is at `servingView pk`, and the
  -- registered `CacheView HandlerCarrier.State` is the view that notices nothing.
  have happend : @appendedOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep
      input (servingNotice pk state.1 input, state.2.1) answer = state.2.1 :=
    @appendedOf_of_cached HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep
      input (servingNotice pk state.1 input, state.2.1) answer answer
      (by
        show HandlerCarrier.cacheOf (servingNotice pk state.1 input) input = some answer
        rw [cacheOf_servingNotice pk state.1 input]
        exact hcached)
  show (pure (answer, (servingNotice pk state.1 input,
      (@appendedOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep input
          (servingNotice pk state.1 input, state.2.1) answer,
        state.2.2 + 1))) : ProbComp (OracleWorld.Range (Sum.inr input) × CountedState)) = _
  rw [happend, noticeAt]
  rfl

/-- **And a miss draws uniformly.** -/
theorem run_inr_fresh (rightKeep : Bytes → HandlerCarrier.State → Prop) (input : Bytes)
    (state : CountedState) (hfresh : cacheAt state input = none) :
    ((countedCarrierRecorder pk rightKeep) (Sum.inr input)).run state =
      (fun answer => (answer, stepAt pk rightKeep state input answer)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput) := by
  classical
  rw [countedCarrierRecorder, CountedHandler.withCount_run,
    @noticingRecorderOf_run_inr_none HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1) hfresh]
  rw [map_eq_bind_pure_comp, bind_assoc, map_eq_bind_pure_comp]
  refine bind_congr fun answer => ?_
  simp only [Function.comp_def, pure_bind]
  rfl

/-! ## The two run-level facts, from the three steps

Both are `OrderingCompose`'s generic lemmas at this handler. Neither is an induction here, which
is the point of having stated them generically: a handler owes the charge its steps. -/

/-- **A run under the carrier handler never fails.** -/
theorem run_mass (rightKeep : Bytes → HandlerCarrier.State → Prop) (β : Type)
    (computation : OracleComp OracleWorld β) (state : CountedState) :
    Pr[⊥ | (simulateQ (countedCarrierRecorder pk rightKeep) computation).run state] = 0 :=
  OrderingCompose.mass_run (countedCarrierRecorder pk rightKeep)
    (OrderingCompose.step_mass (countedCarrierRecorder pk rightKeep) cacheAt
      (stepAt pk rightKeep) (noticeAt pk) (run_inl_mass pk rightKeep)
      (fun input state answer hcached => run_inr_cached pk rightKeep input state answer hcached)
      (fun input state hfresh => run_inr_fresh pk rightKeep input state hfresh))
    computation state

/-! ## The three readings, and why they are payable

The charge reads three things of a state, and all three here are functions of
`BracketedRun.forgetCarrier` — the cache and the two recordings. That is not a convenience. It is
what makes every other law free:

* the **notice** moves the carrier's served set and the counter and nothing else, so it moves
  none of the three;
* a **bracket** writes the framing and nothing else, which is exactly `BracketedRun.Bracket`, so
  it moves none of the three either.

A reading that looked at the framing would be fired by the opening bracket at probability one,
and `OrderingCompose.Neutral` would be false of it. The event the socket wants is the cache-side
disclosure at the end, which is of this form; the carrier's own flag is not, and is not what is
charged. -/

/-- The event: a target-recorded entry is disclosing at the final cache. -/
def Fired (prfSeed : Digest) (key : PublicKey) (state : CountedState) : Prop :=
  LateRate.Served.Fired (SplitWitness.disclosingKeep prfSeed key) (forgetCarrier state)

/-- The potential: the target-recorded entries not yet settled. -/
noncomputable def potentialAt (spent : QueryCache HashSpec → Bytes → Prop)
    (state : CountedState) : Nat :=
  LateRate.Served.potential spent (forgetCarrier state)

/-- The gauge: how long the target recording is. -/
def gaugeAt (state : CountedState) : Nat := LateRate.Served.gauge (forgetCarrier state)

/-- **The notice is invisible to all three**, because it moves neither the cache nor either
recording. -/
theorem forgetCarrier_noticeAt (state : CountedState) (input : Bytes) :
    forgetCarrier (noticeAt pk state input) = forgetCarrier state := by
  rw [forgetCarrier, forgetCarrier, cache_noticeAt pk state input, records_noticeAt pk state input]

theorem fired_noticeAt (prfSeed : Digest) (key : PublicKey) (state : CountedState)
    (input : Bytes) (hfired : Fired prfSeed key (noticeAt pk state input)) :
    Fired prfSeed key state := by
  rw [Fired, forgetCarrier_noticeAt pk state input] at hfired
  exact hfired

theorem potentialAt_noticeAt (spent : QueryCache HashSpec → Bytes → Prop)
    (state : CountedState) (input : Bytes) :
    potentialAt spent (noticeAt pk state input) ≤ potentialAt spent state := by
  rw [potentialAt, potentialAt, forgetCarrier_noticeAt pk state input]

theorem gaugeAt_noticeAt (state : CountedState) (input : Bytes) :
    gaugeAt (noticeAt pk state input) = gaugeAt state := by
  rw [gaugeAt, gaugeAt, forgetCarrier_noticeAt pk state input]

/-- **And so is a bracket**, for the same reason and by the condition it already meets. -/
theorem neutral_of_bracket (prfSeed : Digest) (key : PublicKey)
    (spent : QueryCache HashSpec → Bytes → Prop) {f : CountedState → CountedState}
    (hf : Bracket f) :
    OrderingCompose.Neutral (Fired prfSeed key) (potentialAt spent) gaugeAt f := by
  refine ⟨fun state hfired => ?_, fun state => ?_, fun state => ?_⟩
  · rw [Fired, forgetCarrier_of_bracket hf state] at hfired
    exact hfired
  · rw [potentialAt, potentialAt, forgetCarrier_of_bracket hf state]
  · rw [gaugeAt, gaugeAt, forgetCarrier_of_bracket hf state]

/-- **A fresh step never shortens the target recording.** -/
theorem gaugeAt_stepAt (rightKeep : Bytes → HandlerCarrier.State → Prop) (state : CountedState)
    (input : Bytes) (answer : HashOutput) :
    gaugeAt state ≤ gaugeAt (stepAt pk rightKeep state input answer) := by
  refine List.IsPrefix.length_le ?_
  show state.2.1.2 <+:
    (@appendedOf HandlerCarrier.State (servingView pk) (disclosingKeep pk) rightKeep input
      (servingNotice pk state.1 input, state.2.1) answer).2
  exact @right_prefix_appendedOf HandlerCarrier.State (servingView pk) (disclosingKeep pk)
    rightKeep input (servingNotice pk state.1 input, state.2.1) answer

/-! ## The charge at the carrier's three stages, with one hypothesis left

Everything the charge asks of the handler, of the notice, of the brackets and of the gauge is
discharged above. What remains is the step bound — the one place a rate is actually spent — and
it is a hypothesis here for the same reason the per-walk bound was a hypothesis one layer up:
so that the composition is in hand before the arithmetic is, and nothing has to move when it
arrives. -/

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The ordering charge across the carrier's three stages.** -/
theorem prob_fired_le_threeStage (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (prfSeed : Digest) (key : PublicKey) (spent : QueryCache HashSpec → Bytes → Prop)
    (rate : ℝ≥0∞)
    (hstep : ∀ (state : CountedState) (input : Bytes), cacheAt state input = none →
      ¬ Fired prfSeed key state →
      ∃ bound after : Nat,
        (∀ answer : HashOutput,
            ¬ Fired prfSeed key (stepAt pk rightKeep state input answer) →
              potentialAt spent (stepAt pk rightKeep state input answer) ≤ bound) ∧
          (∀ answer : HashOutput,
              gaugeAt (stepAt pk rightKeep state input answer) = after) ∧
            Pr[fun answer : HashOutput =>
                  Fired prfSeed key (stepAt pk rightKeep state input answer) |
                ($ᵗ HashOutput : ProbComp HashOutput)] + ((bound : Nat) : ℝ≥0∞) * rate ≤
              ((potentialAt spent state : Nat) : ℝ≥0∞) * rate +
                ((after - gaugeAt state : Nat) : ℝ≥0∞) * rate)
    (before : Message → CountedState → CountedState) (afterMap : CountedState → CountedState)
    (hbefore : ∀ request : Message, Bracket (before request)) (hafterMap : Bracket afterMap)
    {β α γ δ : Type}
    (inner : β → QueryImpl (OracleWorld + SigningSpec)
      (WriterT (ω) (StateT SigningLog (OracleComp OracleWorld))))
    (first : OracleComp OracleWorld β)
    (phase : β → OracleComp (OracleWorld + SigningSpec) α)
    (last : β → α → OracleComp OracleWorld γ)
    (outcome : β → α → ω → SigningLog → γ → CountedState → δ)
    (firedFinal : δ → Prop) (gaugeFinal : δ → Nat)
    (hfiredFinal : ∀ (keys : β) (middle : α) (accumulated : ω)
      (log : SigningLog) (final : γ) (state : CountedState),
      firedFinal (outcome keys middle accumulated log final state) → Fired prfSeed key state)
    (hgaugeFinal : ∀ (keys : β) (middle : α) (accumulated : ω)
      (log : SigningLog) (final : γ) (state : CountedState),
      gaugeAt state ≤ gaugeFinal (outcome keys middle accumulated log final state))
    (start : CountedState) (hstart : ¬ Fired prfSeed key start) :
    Pr[firedFinal |
        (simulateQ (countedCarrierRecorder pk rightKeep) first).run start >>= fun keys =>
          (simulateQ (fuseServing (countedCarrierRecorder pk rightKeep) (inner keys.1) before
              afterMap) (phase keys.1)).run ((1 : ω), [], keys.2) >>=
            fun middle =>
              (simulateQ (countedCarrierRecorder pk rightKeep)
                  (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
                (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                  ProbComp δ)] ≤
      ((potentialAt spent start : Nat) : ℝ≥0∞) * rate +
        expected ((simulateQ (countedCarrierRecorder pk rightKeep) first).run start >>=
            fun keys =>
              (simulateQ (fuseServing (countedCarrierRecorder pk rightKeep) (inner keys.1) before
                  afterMap) (phase keys.1)).run ((1 : ω), [], keys.2) >>=
                fun middle =>
                  (simulateQ (countedCarrierRecorder pk rightKeep)
                      (last keys.1 middle.1)).run middle.2.2.2 >>= fun final =>
                    (pure (outcome keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2) :
                      ProbComp δ))
          (fun w => gaugeFinal w - gaugeAt start) * rate :=
  OrderingCompose.prob_fired_le_threeStage (countedCarrierRecorder pk rightKeep) cacheAt
    (stepAt pk rightKeep) (noticeAt pk) (run_inl pk rightKeep) (run_inl_mass pk rightKeep)
    (fun input state answer hcached => run_inr_cached pk rightKeep input state answer hcached)
    (fun input state hfresh => run_inr_fresh pk rightKeep input state hfresh)
    (run_mass pk rightKeep) (Fired prfSeed key) (potentialAt spent) gaugeAt rate
    (fun state input hfired => fired_noticeAt pk prfSeed key state input hfired)
    (fun state input => potentialAt_noticeAt pk spent state input)
    (fun state input => gaugeAt_noticeAt pk state input)
    (fun state input answer => gaugeAt_stepAt pk rightKeep state input answer)
    (fun β inner state result hresult =>
      OrderingCompose.gauge_run (countedCarrierRecorder pk rightKeep) cacheAt
        (stepAt pk rightKeep) (noticeAt pk) (run_inl pk rightKeep)
        (fun input state answer hcached => run_inr_cached pk rightKeep input state answer hcached)
        (fun input state hfresh => run_inr_fresh pk rightKeep input state hfresh) gaugeAt
        (fun state input => gaugeAt_noticeAt pk state input)
        (fun state input answer => gaugeAt_stepAt pk rightKeep state input answer)
        inner state result hresult)
    hstep before afterMap
    (fun request => neutral_of_bracket prfSeed key spent (hbefore request))
    (neutral_of_bracket prfSeed key spent hafterMap)
    inner first phase last outcome firedFinal gaugeFinal hfiredFinal hgaugeFinal start hstart

end SlhDsaSecurity.CarrierCharge

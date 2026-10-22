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

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierCharge

open Security BracketedRun RecorderView CarriedWitness CarrierFiles HandlerCarrier

variable (pk : PublicKey)

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

end SlhDsaSecurity.CarrierCharge

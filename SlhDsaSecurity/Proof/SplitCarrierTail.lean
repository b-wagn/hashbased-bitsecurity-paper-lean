import SlhDsaSecurity.Proof.SplitCounted
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.AnswerCarrier

/-!
# The carrier's tail, with the counter split in two

`CarrierTail.carrierTail` keeps one counter in its handler's state. The answer half's two
charges need two: the structural clause is paid by the queries *outside* the target class and
the coverage clause by those inside, and the two must be read off **one** run or the budget is
spent twice. `SplitCounted.withSplit` is that counter at the handler; this file is the same
three-stage tail under it, and the projection that reads the tail as a run of the shared oracle
with `Security.countQueries (ClassGrowth.splitCost …)` wrapped around the computation.

**Nothing here is a new argument.** Every statement is `CarrierTail`'s with `Nat` replaced by
`Counts` and `hashCost` by `splitCost`, and every proof is the same proof: the counter is an
extra component of the handler's state, `CountedHandler.withExtra` carries it, and the brackets
write the framing and nothing else. The one place the two counters meet —
`SplitCounted.run_withSplit_withCount` — is already proved, so this tail and the counted one are
the same run read two ways, and a charge taken at either may be read at the other.

What the file is *for* is the last theorem: the structural charge at the split tail, stated at
the `outside` slot, in the shape `CoverageCount.prob_bad_or_coverage_le_of_charges` takes.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SplitCarrierTail

open Security RecorderView CarriedWitness PhaseFusion RecordedQueries BracketedRun
open CarrierTail ClassGrowth SplitCounted

/-! ## The shared oracle, counting into two slots

`CountedHandler.romWithCount` is the shared oracle with a counter beside its cache; this is the
same with a pair of slots. It is a separate definition for the reason `romWithCount` is one: the
carrier's state associates the other way, and merging the two would cost a reassociation at
every call site. -/

/-- The shared oracle with a two-slot hash counter beside its cache. -/
noncomputable def romWithSplit (inClass : Bytes → Prop) (inside outside : QueryKind) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec × Counts) ProbComp) :=
  fun queried state => do
    let step ← (KeygenUniform.rom queried).run state.1
    pure (step.1, (step.2, state.2 + splitCost inClass inside outside queried))

theorem romWithSplit_run (inClass : Bytes → Prop) (inside outside : QueryKind)
    (queried : OracleWorld.Domain) (state : QueryCache HashSpec × Counts) :
    (romWithSplit inClass inside outside queried).run state =
      (KeygenUniform.rom queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 + splitCost inClass inside outside queried)) :
          ProbComp (OracleWorld.Range queried × (QueryCache HashSpec × Counts))) := rfl

theorem romWithSplit_step_map (inClass : Bytes → Prop) (inside outside : QueryKind)
    (queried : OracleWorld.Domain) (state : QueryCache HashSpec × Counts) :
    (fun z : OracleWorld.Range queried × (QueryCache HashSpec × Counts) => (z.1, z.2.1)) <$>
        (romWithSplit inClass inside outside queried).run state =
      (KeygenUniform.rom queried).run state.1 := by
  rw [romWithSplit_run, map_eq_bind_pure_comp, bind_assoc]
  simp

set_option maxHeartbeats 1000000 in
/-- **Its slots are `countQueries (splitCost …)`'s count.** `CountedHandler.run_romWithCount_count`
with the pair in place of the number; the counter the run started at is carried for the same
reason, that the tail's three stages add up only when each equation says what it started
from. -/
theorem run_romWithSplit_count (inClass : Bytes → Prop) (inside outside : QueryKind)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : QueryCache HashSpec × Counts,
      (fun z : α × (QueryCache HashSpec × Counts) => ((z.1, z.2.2), z.2.1)) <$>
          (simulateQ (romWithSplit inClass inside outside) computation).run state =
        (fun r : (α × Counts) × QueryCache HashSpec => ((r.1.1, state.2 + r.1.2), r.2)) <$>
          (simulateQ KeygenUniform.rom
            (countQueries (splitCost inClass inside outside) computation)).run state.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, VerificationBudget.countQueries_pure,
      simulateQ_pure, StateT.run_pure, map_pure, add_zero]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, romWithSplit_run,
      bind_assoc, WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind]
    refine bind_congr fun inner => ?_
    rw [pure_bind, ih inner.1 (inner.2, state.2 + splitCost inClass inside outside queried),
      simulateQ_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> (simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) (next inner.1))).run inner.2)
      (funext fun result => ?_)
    show ((result.1.1, state.2 + splitCost inClass inside outside queried + result.1.2),
        result.2) =
      ((result.1.1, state.2 + (splitCost inClass inside outside queried + result.1.2)),
        result.2)
    rw [add_assoc]

set_option maxHeartbeats 1000000 in
/-- **A split-counted handler's slots are `countQueries (splitCost …)`'s count.**
`CountedHandler.run_withCount_count` at the pair. -/
theorem run_withSplit_count {τ : Type} (inClass : Bytes → Prop) (inside outside : QueryKind)
    (impl : QueryImpl OracleWorld (StateT (HandlerCarrier.State × τ) ProbComp))
    (outer' : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (hforget : ServingForget.ForgetsAlong
      (fun state : HandlerCarrier.State × τ => state.1.cache) impl outer')
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ state : HandlerCarrier.State × (τ × Counts),
      (fun z : α × (HandlerCarrier.State × (τ × Counts)) => ((z.1, z.2.2.2), z.2.1.cache)) <$>
          (simulateQ (withSplit inClass inside outside impl) computation).run state =
        (fun r : (α × Counts) × QueryCache HashSpec => ((r.1.1, state.2.2 + r.1.2), r.2)) <$>
          (simulateQ outer'
            (countQueries (splitCost inClass inside outside) computation)).run state.1.cache := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, map_pure, VerificationBudget.countQueries_pure,
      simulateQ_pure, StateT.run_pure, map_pure, add_zero]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, withSplit_run,
      bind_assoc, WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, map_bind,
      ← CountedHandler.forgetsAlong_step (fun s : HandlerCarrier.State × τ => s.1.cache) impl
        outer' hforget queried (state.1, state.2.1), bind_map_left]
    refine bind_congr fun inner => ?_
    rw [pure_bind, ih inner.1
        (inner.2.1, (inner.2.2, state.2.2 + splitCost inClass inside outside queried)),
      simulateQ_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> (simulateQ outer'
      (countQueries (splitCost inClass inside outside) (next inner.1))).run inner.2.1.cache)
      (funext fun result => ?_)
    show ((result.1.1, state.2.2 + splitCost inClass inside outside queried + result.1.2),
        result.2) =
      ((result.1.1, state.2.2 + (splitCost inClass inside outside queried + result.1.2)),
        result.2)
    rw [add_assoc]


/-! ## The tail

The same three stages as `CarrierTail.carrierTail`, under the same recorder, with the counter
split. The shape is forced by the recording exactly as it is there: key generation and
verification run under the handler directly and only the adversary's phase is fused, so that the
inner handler's record and charge belong to the adversary alone. -/

/-- The handler's state, with two slots where the tail's has one. -/
abbrev SplitCountedState : Type :=
  HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts)

/-- The projection the tail ends at: the cache and the two recordings, with the carrier's served
set, its framing and the counter dropped. `BracketedRun.forgetCarrier` at the pair. -/
def forgetSplitCarrier (state : SplitCountedState) : SplitPrefix.SplitState :=
  (state.1.cache, state.2.1)

/-- The handler the split tail runs under: the recorder that notices, at the walk's key,
counting into two slots. -/
noncomputable def splitHandlerAt (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk) :
    QueryImpl OracleWorld (StateT SplitCountedState ProbComp) :=
  SplitCounted.splitCarrierRecorder (keyAt walk) inClass inside outside (rightKeep walk)

/-- **The tail, with the counter split.** -/
noncomputable def splitCarrierTail (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    ProbComp (((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState) :=
  (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
    (startAt walk.2, (([], []), 0)) >>= fun keys =>
    (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk)
        (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
        ServedAgreement.startServingOn ServedAgreement.stopServingOn)
      (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun middle =>
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
        (countRecorded verifierCost
          (Scheme.verify keys.1.2 middle.1.message middle.1.signature))).run
        middle.2.2.2 >>= fun final =>
        (pure ((({
              forgery := middle.1
              signed := middle.2.2.1
              verified := final.1.1
              counts := (Multiplicative.toAdd middle.2.1).1 + final.1.2.1 },
            (Multiplicative.toAdd middle.2.1).2 + final.1.2.2), final.2.2.2),
          forgetSplitCarrier final.2) :
          ProbComp (((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState))

/-! ## The stages project, exactly as they do at one counter -/

theorem split_stage_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitCountedState) :
    (fun z : α × SplitCountedState => ((z.1, z.2.2.2), z.2.1.cache)) <$>
        (simulateQ (splitHandlerAt inClass inside outside rightKeep walk) computation).run
          state =
      (fun r : (α × Counts) × QueryCache HashSpec => ((r.1.1, state.2.2 + r.1.2), r.2)) <$>
        (simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run state.1.cache :=
  run_withSplit_count inClass inside outside
    (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk))
    KeygenUniform.rom (CarrierFiles.forgetsAlong_carrierRecorder (keyAt walk) (rightKeep walk))
    computation state

theorem splitHandlerAt_step_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (queried : OracleWorld.Domain) (state : SplitCountedState) :
    (fun z : OracleWorld.Range queried × SplitCountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        ((splitHandlerAt inClass inside outside rightKeep walk) queried).run state =
      (romWithSplit inClass inside outside queried).run (state.1.cache, state.2.2) := by
  rw [splitHandlerAt, SplitCounted.splitCarrierRecorder, SplitCounted.withSplit_run,
    romWithSplit_run, map_eq_bind_pure_comp, bind_assoc]
  show _ = (KeygenUniform.rom queried).run
      (CacheView.cacheOf (σ := HandlerCarrier.State) (state.1, state.2.1).1) >>= _
  rw [← CarrierFiles.noticingRecorderOf_forget_step (keyAt walk) (rightKeep walk) queried
      (state.1, state.2.1), map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun step => ?_
  simp only [Function.comp_def, pure_bind]
  rfl

theorem forgetsAlong_split (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk) :
    ServingForget.ForgetsAlong (fun state : SplitCountedState => (state.1.cache, state.2.2))
      (splitHandlerAt inClass inside outside rightKeep walk)
      (romWithSplit inClass inside outside) := by
  intro β computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind,
      ← splitHandlerAt_step_forget inClass inside outside rightKeep walk queried state,
      bind_map_left]
    exact bind_congr fun step => ih step.1 step.2

/-- **The brackets keep the cache and both slots.** -/
theorem startServingOn_cacheSplit (request : Message) (state : SplitCountedState) :
    ((ServedAgreement.startServingOn request state).1.cache,
        (ServedAgreement.startServingOn request state).2.2) =
      (state.1.cache, state.2.2) := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

theorem stopServingOn_cacheSplit (state : SplitCountedState) :
    ((ServedAgreement.stopServingOn state).1.cache,
      (ServedAgreement.stopServingOn (τ := (DigestTape.Record × DigestTape.Record) × Counts)
        state).2.2) = (state.1.cache, state.2.2) := rfl

theorem split_middle_forget {α : Type} (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (log : SigningLog) (state : SplitCountedState) :
    (fun step : α × (Multiplicative Tally × SigningLog × SplitCountedState) =>
        (step.1, (step.2.1, step.2.2.1, (step.2.2.2.1.cache, step.2.2.2.2.2)))) <$>
      (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk) inner
        ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
        (accumulated, log, state) =
      (simulateQ (fuse (romWithSplit inClass inside outside) inner) computation).run
        (accumulated, log, (state.1.cache, state.2.2)) :=
  ServingForget.run_fuseServing_map (fun s : SplitCountedState => (s.1.cache, s.2.2))
    (splitHandlerAt inClass inside outside rightKeep walk) (romWithSplit inClass inside outside)
    inner ServedAgreement.startServingOn ServedAgreement.stopServingOn
    startServingOn_cacheSplit stopServingOn_cacheSplit
    (forgetsAlong_split inClass inside outside rightKeep walk) computation accumulated log state

/-! ## The three stages as binds -/

theorem split_first_stage_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (fun z : α × SplitCountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        (simulateQ (splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) =
      (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) :=
  forgetsAlong_split inClass inside outside rightKeep walk computation
    (startAt walk.2, (([], []), 0))

theorem split_first_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) =
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp (α × (QueryCache HashSpec × Counts))) := by
  rw [← split_first_stage_forget inClass inside outside rightKeep walk computation,
    map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
theorem split_middle_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (adversary : Adversary) (keys : (SecretKey × PublicKey) × SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside)
        (((simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          (adversary.main keys.1.2)).run).run [])).run (keys.2.1.cache, keys.2.2.2) =
      (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun step =>
        (pure (((step.1, step.2.1), step.2.2.1), (step.2.2.2.1.cache, step.2.2.2.2.2)) :
          ProbComp (((Forgery × Multiplicative Tally) × SigningLog) ×
            (QueryCache HashSpec × Counts))) := by
  rw [PhaseFusion.run_phase_fused (romWithSplit inClass inside outside)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) [] (keys.2.1.cache, keys.2.2.2),
    ← split_middle_forget inClass inside outside rightKeep walk
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) 1 [] keys.2, Functor.map_map, map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
theorem split_last_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (pk : PublicKey) (forgery : Forgery) (state : SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside) (countRecorded verifierCost
        (Scheme.verify pk forgery.message forgery.signature))).run
        (state.1.cache, state.2.2) =
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk)
          (countRecorded verifierCost
            (Scheme.verify pk forgery.message forgery.signature))).run state >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp ((Bool × Tally) × (QueryCache HashSpec × Counts))) := by
  rw [← forgetsAlong_split inClass inside outside rightKeep walk
      (countRecorded verifierCost (Scheme.verify pk forgery.message forgery.signature)) state,
    map_eq_bind_pure_comp]
  rfl



/-! ## The assembly

Both sides are three-stage runs over the same computation, so the composition is a composition.
`run_romWithSplit_recorded` puts the shared oracle's side at the split handler — the slots move
from `countQueries`, wrapped around the computation, into the handler's own state, which is
where the tail keeps them — and after that the two sides differ only in the handler. -/

attribute [local irreducible] RecordedTail.recordedAfterSeeds Scheme.keygenInternal
  Scheme.verify Scheme.sign Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **The split-counted shared oracle's slots are `countQueries (splitCost …)`'s**, at the run
the tail is compared against. `CarrierTail.recordedTail_eq_counted` at the pair, and the same
one-line reason: the run starts at an empty counter, so the counter it started from adds
nothing. -/
theorem run_romWithSplit_recorded (inClass : Bytes → Prop) (inside outside : QueryKind)
    (adversary : Adversary) (walk : Walk) :
    (fun z : (Outcome × Multiset Bytes) × (QueryCache HashSpec × Counts) =>
        ((z.1, z.2.2), z.2.1)) <$>
        (simulateQ (romWithSplit inClass inside outside)
          (RecordedTail.recordedAfterSeeds adversary walk.1.1)).run (walk.2, 0) =
      (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2 := by
  rw [run_romWithSplit_count inClass inside outside
      (RecordedTail.recordedAfterSeeds adversary walk.1.1) (walk.2, 0),
    show (fun r : ((Outcome × Multiset Bytes) × Counts) × QueryCache HashSpec =>
        ((r.1.1, (0 : Counts) + r.1.2), r.2)) = id from funext fun r => by rw [zero_add]; rfl,
    id_map]

set_option maxHeartbeats 1000000 in
/-- **The split tail is a split-counted run of the shared oracle**, once its recordings are
dropped. `CarrierTail.forget_carrierTail` at the pair, matched stage for stage by the three bind
laws above. -/
theorem forget_splitCarrierTail (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
        (z.1, z.2.1)) <$>
        splitCarrierTail inClass inside outside rightKeep adversary walk =
      (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2 := by
  rw [← run_romWithSplit_recorded inClass inside outside adversary walk,
    run_recordedAfterSeeds_split (romWithSplit inClass inside outside) adversary walk.1.1
      (walk.2, 0),
    split_first_stage_bind inClass inside outside rightKeep walk
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2),
    splitCarrierTail]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun keys => ?_
  rw [split_middle_stage_bind inClass inside outside rightKeep walk adversary keys]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun middle => ?_
  rw [split_last_stage_bind inClass inside outside rightKeep walk keys.1.2 middle.1
    middle.2.2.2]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun final => ?_
  rfl



/-! ## The structural charge, at the outside slot

This is what the file is for. `CoverageCount.prob_bad_or_coverage_le_of_charges` takes the
structural clause at the expected value of the **outside** slot of the run's own counter, and
that is exactly `ClassExpectation.prob_bad_le_expected_cost` at `splitCost`'s complementary
slot — the same proposition `ClassExpectation.prob_bad_le_expected_outside` reads at a one-stage
run of the shared oracle.

**Nothing is re-argued at the tail.** `forget_splitCarrierTail` says the tail *is* that run once
its recordings are dropped, `GrowthCharge.Bad` reads only the cache, and the slot is read off
the value — so both sides of the charge transport along one map, the event by `probEvent_map`
and the count by `ClassExpectation.expected_map`. The bracketing, the notice and the filing are
invisible to this charge, and that is the point of having proved the projection first.

The class is left free. Nothing here reads it beyond `hbadClass`, so narrowing the target class
does not touch this charge.

**And the two slots are not asked to be distinct.** `ClassExpectation.prob_bad_le_expected_outside`
needs `inside ≠ outside` because it crosses from the plainly counted run to the split one and
the crossing adds the slots; this charge never leaves the split run, so it needs only that the
outside slot is charged for an out-of-class query, which `splitCost_outside` gives whatever the
other slot is. The distinctness is still needed where the two counts are added — the budget is
where a shared slot would be paid for twice — and that is `hshare`'s business, not this one's. -/

open scoped Classical in
/-- **The structural charge at the split tail, at the outside slot.** -/
theorem prob_bad_splitCarrierTail_le (inClass : Bytes → Prop) {inside outside : QueryKind}
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ENNReal))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) (hclean : GrowthCharge.CleanBad bad walk.2) :
    Pr[fun result : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad
          (((result.1.1, result.1.2 inside + result.1.2 outside) :
            (Outcome × Multiset Bytes) × Nat),
            RecorderView.CacheView.cacheOf result.2.1) |
        splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      ClassExpectation.expected (splitCarrierTail inClass inside outside rightKeep adversary walk)
          (fun result => result.1.2 outside) / ((2 ^ 128 : Nat) : ENNReal) := by
  classical
  have hmap := forget_splitCarrierTail inClass inside outside rightKeep adversary walk
  have hprob : Pr[fun result : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
      GrowthCharge.Bad bad
        (((result.1.1, result.1.2 inside + result.1.2 outside) :
          (Outcome × Multiset Bytes) × Nat),
          RecorderView.CacheView.cacheOf result.2.1) |
      splitCarrierTail inClass inside outside rightKeep adversary walk] =
      Pr[GrowthCharge.Bad bad |
        (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
          (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2] := by
    rw [← hmap, probEvent_map]
    rfl
  have hcount : ClassExpectation.expected
      ((simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2)
        (fun result => result.1.2 outside) =
      ClassExpectation.expected
        (splitCarrierTail inClass inside outside rightKeep adversary walk)
        (fun result => result.1.2 outside) := by
    rw [← hmap, ClassExpectation.expected_map]
  rw [hprob, ← hcount, ← mul_one_div]
  exact ClassExpectation.prob_bad_le_expected_cost (fun input => ¬ inClass input) bad _
    (splitCost inClass inside outside) outside
    (fun input hmember => by rw [splitCost_outside inClass inside outside input hmember])
    hrate hbadClass (RecordedTail.recordedAfterSeeds adversary walk.1.1) walk.2 hclean



/-! ## Where it meets the other charge

The composition is `CoverageCount.prob_bad_or_coverage_le_of_charges` and nothing else: the
structural clause is discharged here, the coverage clause is the hypothesis, and the budget is
pathwise. Stating it is how the charge above is *checked* against its consumer rather than
asserted to fit — the two had better agree on the slot, on the summed counter inside the event,
and on which cache the event reads, and the only way to know is to apply one to the other. -/

open scoped Classical in
/-- **The answer half's bound at the split tail**, with the structural charge discharged and the
coverage charge taken as given. -/
theorem answerBound_splitCarrierTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ENNReal))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) (hclean : GrowthCharge.CleanBad bad walk.2)
    (coverage : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState → Prop)
    (constant : ENNReal)
    (hcoverage : Pr[coverage |
        splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      constant + ClassExpectation.expected
        (splitCarrierTail inClass inside outside rightKeep adversary walk)
        (fun result => result.1.2 inside) / ((2 ^ 128 : Nat) : ENNReal))
    (budget : Nat)
    (hshare : ∀ result ∈ support
      (splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.2 outside + result.1.2 inside ≤ budget) :
    Pr[fun result : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad
            (((result.1.1, result.1.2 inside + result.1.2 outside) :
              (Outcome × Multiset Bytes) × Nat),
              RecorderView.CacheView.cacheOf result.2.1) ∨ coverage result |
        splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      ((budget : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) + constant :=
  CoverageCount.prob_bad_or_coverage_le_of_charges bad inside outside
    (splitCarrierTail inClass inside outside rightKeep adversary walk) coverage constant
    (prob_bad_splitCarrierTail_le inClass bad hrate hbadClass rightKeep adversary walk hclean)
    hcoverage budget hshare



/-! ## The split tail is the tail

The charge above is stated at a run nothing else is stated at, and that is only safe because
the two runs are one run read two ways. `SplitCounted.sumSlots` adds the slots, the split
handler forgets to the counted one along it, and the brackets commute with it because they
write the framing and summing writes the counter. So the three stages chain exactly as they do
in `CarrierTail.forget_carrierTail` and no induction is repeated.

**Here the slots do have to be distinct.** `forgetsAlong_sumSlots` is `run_withSplit_withCount`,
which needs `inside ≠ outside`: a shared slot would be added to itself. That is the same place
the distinctness is needed in the budget, and it is the only place — the charge itself does not
ask for it. -/

set_option maxHeartbeats 1000000 in
theorem sum_first_stage_bind (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitCountedState) :
    (simulateQ (CarrierTail.handlerAt rightKeep walk) computation).run
        (SplitCounted.sumSlots inside outside state) =
      (simulateQ (splitHandlerAt inClass inside outside rightKeep walk) computation).run
          state >>= fun z =>
        (pure (z.1, SplitCounted.sumSlots inside outside z.2) :
          ProbComp (α × BracketedRun.CountedState)) := by
  rw [CarrierTail.handlerAt, CarrierFiles.countedCarrierRecorder, splitHandlerAt,
    SplitCounted.splitCarrierRecorder,
    ← SplitCounted.forgetsAlong_sumSlots inClass hne
      (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
        (disclosingKeep (keyAt walk)) (rightKeep walk)) computation state,
    map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
theorem sum_middle_stage_bind (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (adversary : Adversary) (keys : (SecretKey × PublicKey) × SplitCountedState) :
    (simulateQ (fuseServing (CarrierTail.handlerAt rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
        (adversary.main keys.1.2)).run
        (1, [], SplitCounted.sumSlots inside outside keys.2) =
      (simulateQ (fuseServing (splitHandlerAt inClass inside outside rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun step =>
        (pure (step.1, (step.2.1, step.2.2.1,
            SplitCounted.sumSlots inside outside step.2.2.2)) :
          ProbComp (Forgery × (Multiplicative Tally × SigningLog ×
            BracketedRun.CountedState))) := by
  rw [CarrierTail.handlerAt, CarrierFiles.countedCarrierRecorder, splitHandlerAt,
    SplitCounted.splitCarrierRecorder,
    ← ServingForget.run_fuseServing_conj (SplitCounted.sumSlots inside outside) _ _
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      ServedAgreement.startServingOn ServedAgreement.stopServingOn
      ServedAgreement.startServingOn ServedAgreement.stopServingOn
      (SplitCounted.sumSlots_startServingOn inside outside)
      (SplitCounted.sumSlots_stopServingOn inside outside)
      (SplitCounted.forgetsAlong_sumSlots inClass hne
        (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
          (disclosingKeep (keyAt walk)) (rightKeep walk)))
      (adversary.main keys.1.2) 1 [] keys.2,
    map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The split tail is the tail, with the counter split.** -/
theorem sum_splitCarrierTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
        ((z.1.1, z.1.2 inside + z.1.2 outside), z.2)) <$>
        splitCarrierTail inClass inside outside rightKeep adversary walk =
      CarrierTail.carrierTail rightKeep adversary walk := by
  rw [CarrierTail.carrierTail,
    show (CarrierTail.startAt walk.2, ((([], []) : DigestTape.Record × DigestTape.Record),
        (0 : Nat))) =
      SplitCounted.sumSlots inside outside (CarrierTail.startAt walk.2, (([], []), 0)) from rfl,
    sum_first_stage_bind inClass hne rightKeep walk
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
      (CarrierTail.startAt walk.2, (([], []), 0)),
    splitCarrierTail]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun keys => ?_
  rw [sum_middle_stage_bind inClass hne rightKeep walk adversary keys]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun middle => ?_
  rw [sum_first_stage_bind inClass hne rightKeep walk
    (countRecorded verifierCost (Scheme.verify keys.1.2 middle.1.message middle.1.signature))
    middle.2.2.2]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun final => ?_
  rfl



/-! ## And so at the run the answer half's bound is owed at

`AnswerCarrier.answerCarrierRun` is `AnswerShape.forgetRecord` over the tail, so it is one
further map from the split tail. Composed with `sum_splitCarrierTail` that is a single map out
of the split run, which is what `hsplit` and the coverage charge — both stated at
`answerCarrierRun` — travel along by `probEvent_map`, with no new argument at either end.

Stated as an equality of *computations*, and the two forgetting **functions** are all that is
compared: the three stages are never unfolded, which is the lesson of
`AnswerCarrier.map_answerCarrierRun_eq_tail` one map further down. -/

theorem map_splitCarrierTail_eq_answerCarrierRun (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : ((Outcome × Multiset Bytes) × Counts) × SplitPrefix.SplitState =>
        AnswerShape.forgetRecord ((z.1.1, z.1.2 inside + z.1.2 outside), z.2)) <$>
        splitCarrierTail inClass inside outside rightKeep adversary walk =
      AnswerCarrier.answerCarrierRun rightKeep adversary walk := by
  rw [AnswerCarrier.answerCarrierRun,
    ← sum_splitCarrierTail inClass hne rightKeep adversary walk, Functor.map_map]


end SlhDsaSecurity.SplitCarrierTail

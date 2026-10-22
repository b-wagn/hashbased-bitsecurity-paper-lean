import SlhDsaSecurity.Proof.SplitCounted
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.AnswerCarrier
import SlhDsaSecurity.Proof.SplitTail

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


/-! ## The tail is `SplitTail.splitCarrierTail`

**There is only one split tail and it is not this file's.** An earlier draft of this file built
its own, with the slots carried inside the value instead of beside it; `SplitTail` had already
built the same three stages at the same handler with the same brackets, and `hshare` and the
coverage charge are proved there. Two shapes for one object is the failure a guessed count
produces, so this file keeps none of its own: everything below is stated at
`SplitTail.splitCarrierTail`, and what survived the retargeting is what was never about the
tail — the shared oracle with two slots, and the laws the *handler* satisfies. -/

/-- The handler's state, with two slots where the tail's has one. -/
abbrev SplitCountedState : Type :=
  HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Counts)

/-! ## The stages project, exactly as they do at one counter -/

theorem rom_stage_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitCountedState) :
    (fun z : α × SplitCountedState => ((z.1, z.2.2.2), z.2.1.cache)) <$>
        (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) computation).run
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
        ((SplitTail.splitHandlerAt inClass inside outside rightKeep walk) queried).run state =
      (romWithSplit inClass inside outside queried).run (state.1.cache, state.2.2) := by
  rw [SplitTail.splitHandlerAt, SplitCounted.splitCarrierRecorder, SplitCounted.withSplit_run,
    romWithSplit_run, map_eq_bind_pure_comp, bind_assoc]
  show _ = (KeygenUniform.rom queried).run
      (CacheView.cacheOf (σ := HandlerCarrier.State) (state.1, state.2.1).1) >>= _
  rw [← CarrierFiles.noticingRecorderOf_forget_step (keyAt walk) (rightKeep walk) queried
      (state.1, state.2.1), map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun step => ?_
  simp only [Function.comp_def, pure_bind]
  rfl

theorem forgetsAlong_romWithSplit (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk) :
    ServingForget.ForgetsAlong (fun state : SplitCountedState => (state.1.cache, state.2.2))
      (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
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

theorem rom_middle_forget {α : Type} (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (log : SigningLog) (state : SplitCountedState) :
    (fun step : α × (Multiplicative Tally × SigningLog × SplitCountedState) =>
        (step.1, (step.2.1, step.2.2.1, (step.2.2.2.1.cache, step.2.2.2.2.2)))) <$>
      (simulateQ (fuseServing (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) inner
        ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
        (accumulated, log, state) =
      (simulateQ (fuse (romWithSplit inClass inside outside) inner) computation).run
        (accumulated, log, (state.1.cache, state.2.2)) :=
  ServingForget.run_fuseServing_map (fun s : SplitCountedState => (s.1.cache, s.2.2))
    (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) (romWithSplit inClass inside outside)
    inner ServedAgreement.startServingOn ServedAgreement.stopServingOn
    startServingOn_cacheSplit stopServingOn_cacheSplit
    (forgetsAlong_romWithSplit inClass inside outside rightKeep walk) computation accumulated log state

/-! ## The three stages as binds -/

theorem rom_first_stage_forget (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (fun z : α × SplitCountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) =
      (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) :=
  forgetsAlong_romWithSplit inClass inside outside rightKeep walk computation
    (startAt walk.2, (([], []), 0))

theorem rom_first_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) :
    (simulateQ (romWithSplit inClass inside outside) computation).run (walk.2, 0) =
      (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp (α × (QueryCache HashSpec × Counts))) := by
  rw [← rom_first_stage_forget inClass inside outside rightKeep walk computation,
    map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
theorem rom_middle_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (adversary : Adversary) (keys : (SecretKey × PublicKey) × SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside)
        (((simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          (adversary.main keys.1.2)).run).run [])).run (keys.2.1.cache, keys.2.2.2) =
      (simulateQ (fuseServing (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun step =>
        (pure (((step.1, step.2.1), step.2.2.1), (step.2.2.2.1.cache, step.2.2.2.2.2)) :
          ProbComp (((Forgery × Multiplicative Tally) × SigningLog) ×
            (QueryCache HashSpec × Counts))) := by
  rw [PhaseFusion.run_phase_fused (romWithSplit inClass inside outside)
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) [] (keys.2.1.cache, keys.2.2.2),
    ← rom_middle_forget inClass inside outside rightKeep walk
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) 1 [] keys.2, Functor.map_map, map_eq_bind_pure_comp]
  rfl

set_option maxHeartbeats 1000000 in
theorem rom_last_stage_bind (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (pk : PublicKey) (forgery : Forgery) (state : SplitCountedState) :
    (simulateQ (romWithSplit inClass inside outside) (countRecorded verifierCost
        (Scheme.verify pk forgery.message forgery.signature))).run
        (state.1.cache, state.2.2) =
      (simulateQ (SplitTail.splitHandlerAt inClass inside outside rightKeep walk)
          (countRecorded verifierCost
            (Scheme.verify pk forgery.message forgery.signature))).run state >>= fun z =>
        (pure (z.1, (z.2.1.cache, z.2.2.2)) :
          ProbComp ((Bool × Tally) × (QueryCache HashSpec × Counts))) := by
  rw [← forgetsAlong_romWithSplit inClass inside outside rightKeep walk
      (countRecorded verifierCost (Scheme.verify pk forgery.message forgery.signature)) state,
    map_eq_bind_pure_comp]
  rfl

/-! ## The assembly

`SplitTail.splitCarrierTail` is three stages over the same computation as a run of the shared
oracle with the two slots, so the composition is a composition. `run_romWithSplit_recorded` puts
the oracle's side at the split handler — the slots move from `countQueries`, wrapped around the
computation, into the handler's own state, which is where the tail keeps them — and after that
the two sides differ only in the handler. -/

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
dropped and its slots are read out of the state. `CarrierTail.forget_carrierTail` at the pair,
matched stage for stage by the three bind laws above. -/
theorem forget_splitCarrierTail (inClass : Bytes → Prop) (inside outside : QueryKind)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        ((z.1.1.1, z.2), z.1.2.1)) <$>
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk =
      (simulateQ KeygenUniform.rom (countQueries (splitCost inClass inside outside)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2 := by
  rw [← run_romWithSplit_recorded inClass inside outside adversary walk,
    run_recordedAfterSeeds_split (romWithSplit inClass inside outside) adversary walk.1.1
      (walk.2, 0),
    rom_first_stage_bind inClass inside outside rightKeep walk
      (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2),
    SplitTail.splitCarrierTail]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun keys => ?_
  rw [rom_middle_stage_bind inClass inside outside rightKeep walk adversary keys]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun middle => ?_
  rw [rom_last_stage_bind inClass inside outside rightKeep walk keys.1.2 middle.1
    middle.2.2.2]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun final => ?_
  rfl

/-! ## The structural charge, at the outside slot

This is what the file is for. The answer half's two charges meet at the expected value of one
slot each, and this is the outside one: `ClassExpectation.prob_bad_le_expected_cost` at
`splitCost`'s complementary slot, the same proposition
`ClassExpectation.prob_bad_le_expected_outside` reads at a one-stage run of the shared oracle.

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
other slot is. The distinctness is needed where the two counts are added — the budget is where a
shared slot would be paid for twice — and in `SplitTail.map_splitCarrierTail`, which adds them.
Not here. -/

open scoped Classical in
/-- **The structural charge at the split tail, at the outside slot.** -/
theorem prob_bad_splitCarrierTail_le (inClass : Bytes → Prop) {inside outside : QueryKind}
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ENNReal))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) (hclean : GrowthCharge.CleanBad bad walk.2) :
    Pr[fun result : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        GrowthCharge.Bad bad (result.1.1, result.1.2.1) |
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      ClassExpectation.expected
          (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk)
          (fun result => result.2 outside) / ((2 ^ 128 : Nat) : ENNReal) := by
  classical
  have hmap := forget_splitCarrierTail inClass inside outside rightKeep adversary walk
  have hprob :
      Pr[fun result : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
          GrowthCharge.Bad bad (result.1.1, result.1.2.1) |
          SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk] =
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
        (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk)
        (fun result => result.2 outside) := by
    rw [← hmap, ClassExpectation.expected_map]
  rw [hprob, ← hcount, ← mul_one_div]
  exact ClassExpectation.prob_bad_le_expected_cost (fun input => ¬ inClass input) bad _
    (splitCost inClass inside outside) outside
    (fun input hmember => by rw [splitCost_outside inClass inside outside input hmember])
    hrate hbadClass (RecordedTail.recordedAfterSeeds adversary walk.1.1) walk.2 hclean

/-! ## And so at the run the answer half's bound is owed at

`AnswerCarrier.answerCarrierRun` is `AnswerShape.forgetRecord` over the tail, so it is one
further map from the split tail. Composed with `SplitTail.map_splitCarrierTail` that is a single
map out of the split run, which is what `hsplit` — stated at `answerCarrierRun` — travels along
by `probEvent_map`, with no new argument at either end. -/

theorem map_splitCarrierTail_eq_answerCarrierRun (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) :
    (fun z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        AnswerShape.forgetRecord z.1) <$>
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk =
      AnswerCarrier.answerCarrierRun rightKeep adversary walk := by
  rw [AnswerCarrier.answerCarrierRun,
    ← SplitTail.map_splitCarrierTail inClass hne rightKeep adversary walk, Functor.map_map]

/-! ## Where the two charges meet, at the canonical tail

Both charges are now proved at the same run — the structural one above, the coverage one at
`SplitTail.prob_splitCarrierTail_targetCovered_le` — and `SplitTail.splitCarrierTail_share` says
their counts sit inside the tail's own work count with nothing assumed. So the composition is
`CoverageCount.prob_bad_or_coverage_le_of_two_charges` and the only thing left to supply is a
bound on that work count, which is what a budget *is*. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, met at the split tail.** -/
theorem answerBound_splitTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ENNReal))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) (hclean : GrowthCharge.CleanBad bad walk.2)
    (hrightClass : ∀ (input : Bytes) (view : HandlerCarrier.State),
      rightKeep walk input view → inClass input)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hwork : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.1.2 ≤ budget) :
    Pr[fun result : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        GrowthCharge.Bad bad (result.1.1, result.1.2.1) ∨
          BlockViews.TargetCovered result.1 |
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      ((budget : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
        (1 : ENNReal) / 2 ^ 141 := by
  classical
  refine CoverageCount.prob_bad_or_coverage_le_of_two_charges
    (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk) _ _
    ((1 : ENNReal) / 2 ^ 141) (fun result => result.2 outside)
    (fun result => result.1.2.2.2.length) budget
    (prob_bad_splitCarrierTail_le inClass bad hrate hbadClass rightKeep adversary walk hclean)
    (SplitTail.prob_splitCarrierTail_targetCovered_le inClass hne rightKeep adversary walk
      leftLength rightLength hcap hleftBound hrightBound) ?_
  intro result hresult
  have hshare := SplitTail.splitCarrierTail_share inClass inside outside rightKeep adversary
    walk hrightClass result hresult
  have hbudget := hwork result hresult
  omega

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's bound at the split tail, with the narrowing's leftover excluded.** The
`AnswerCarrier.answerBoundSeed_of_charges` analogue at the canonical object: same three lines,
and `hsplit` may be taken at `AnswerCarrier.answerCarrierRun` and carried here by
`map_splitCarrierTail_eq_answerCarrierRun`, because the event factors through
`AnswerShape.forgetRecord`. -/
theorem answerBoundSeed_splitTail (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ENNReal))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (adversary : Adversary)
    (walk : Walk) (hclean : GrowthCharge.CleanBad bad walk.2)
    (hrightClass : ∀ (input : Bytes) (view : HandlerCarrier.State),
      rightKeep walk input view → inClass input)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.2.2.1.length ≤ leftLength)
    (hrightBound : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.2.2.2.length ≤ rightLength)
    (budget : Nat)
    (hwork : ∀ result ∈ support
      (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      result.1.1.2 ≤ budget)
    (hsplit : ∀ result ∈ support
        (SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk),
      RoutedSplit.AnswerBad ((walk.1, (AnswerShape.forgetRecord result.1).1),
            (AnswerShape.forgetRecord result.1).2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((AnswerShape.forgetRecord result.1).1,
              (AnswerShape.forgetRecord result.1).2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (AnswerShape.forgetRecord result.1) →
        GrowthCharge.Bad bad (result.1.1, result.1.2.1) ∨
          BlockViews.TargetCovered result.1) :
    Pr[fun result : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts =>
        RoutedSplit.AnswerBad ((walk.1, (AnswerShape.forgetRecord result.1).1),
            (AnswerShape.forgetRecord result.1).2.1) ∧
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((AnswerShape.forgetRecord result.1).1,
              (AnswerShape.forgetRecord result.1).2.1) ∧
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (AnswerShape.forgetRecord result.1) |
        SplitTail.splitCarrierTail inClass inside outside rightKeep adversary walk] ≤
      ((budget : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
        (1 : ENNReal) / 2 ^ 141 :=
  le_trans (probEvent_mono hsplit)
    (answerBound_splitTail inClass hne bad hrate hbadClass rightKeep adversary walk hclean
      hrightClass leftLength rightLength hcap hleftBound hrightBound budget hwork)

end SlhDsaSecurity.SplitCarrierTail

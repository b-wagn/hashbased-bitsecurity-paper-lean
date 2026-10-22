import SlhDsaSecurity.Proof.BracketedRun
import SlhDsaSecurity.Proof.CarrierFiles
import SlhDsaSecurity.Proof.RecordedTail

/-!
# The tail the ordering term reads, at the carrier

`FusedCoverage.fusedTail` is the game under `SplitPrefix.recorder`, in one run, because the game
is one computation. This is the same tail at the carrier: the game under the recorder that
notices, counting, with the adversary's phase fused and bracketed so that the signing oracle can
raise and lower a framing around its own sub-run.

**Three stages, and the shape is forced by the recording.** `PhaseFusion.fuse`'s `inl` branch
runs the inner handler before the outer one, and the inner handler here records and charges. Key
generation lifted into the fused computation would have its queries charged to the adversary's
record and counted as its work, so key generation and verification run under the handler
directly and only the adversary's phase is fused. `BracketedRun.IsBracketedRecorderRun` is that
shape, and `isBracketedRecorderRun` below is this tail at it — by `rfl`, because the tail was
written to the predicate rather than fitted to it afterwards.

**What differs from `FusedCoverage.fusedTail`, and what does not.** The value is the same:
`Outcome`, the adversary-and-verifier record beside it, and the total hash count — read from the
handler's counter rather than from `countAllHashes`, because a bracketed game is not one
computation. The state is the same `SplitPrefix.SplitState`: the cache and the two recordings,
with the carrier's served set, its framing and the counter projected away by
`BracketedRun.forgetCarrier`.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierTail

open Security RecorderView CarriedWitness PhaseFusion RecordedQueries BracketedRun

/-- The carrier a run starts from: the walk's cache, nothing served, nothing in flight. -/
def startAt (cache : QueryCache HashSpec) : HandlerCarrier.State :=
  { cache := cache, served := 0, framing := none }

@[simp] theorem cache_startAt (cache : QueryCache HashSpec) : (startAt cache).cache = cache := rfl

/-- The key the walk generates, which both tests are read at. -/
noncomputable abbrev keyAt (walk : Walk) : PublicKey :=
  SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2

/-- The handler the tail runs under: the recorder that notices, at the walk's key, counting. -/
noncomputable def handlerAt (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) : QueryImpl OracleWorld (StateT CountedState ProbComp) :=
  CarrierFiles.countedCarrierRecorder (keyAt walk) (rightKeep walk)

/-- **The tail.** -/
noncomputable def carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) : LateProbes.FusedTail :=
  fun adversary walk =>
    (simulateQ (handlerAt rightKeep walk)
        (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)).run
      (startAt walk.2, (([], []), 0)) >>= fun keys =>
      (simulateQ (fuseServing (handlerAt rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
        (adversary.main keys.1.2)).run (1, [], keys.2) >>= fun middle =>
        (simulateQ (handlerAt rightKeep walk) (countRecorded verifierCost
          (Scheme.verify keys.1.2 middle.1.message middle.1.signature))).run
          middle.2.2.2 >>= fun final =>
          (pure ((({
                forgery := middle.1
                signed := middle.2.2.1
                verified := final.1.1
                counts := (Multiplicative.toAdd middle.2.1).1 + final.1.2.1 },
              (Multiplicative.toAdd middle.2.1).2 + final.1.2.2), final.2.2.2),
            forgetCarrier final.2) :
            ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState))

/-! ## The brackets meet their one condition

`ServedAgreement.startServingOn` writes the framing and `stopServingOn` clears it. Neither
touches the cache and neither touches either recording, which is all `BracketedRun.Bracket`
asks and all `ServingForget.run_fuseServing_map` asks. -/

theorem bracket_startServingOn (request : Message) :
    Bracket (ServedAgreement.startServingOn (τ := (DigestTape.Record × DigestTape.Record) × Nat)
      request) := by
  intro state
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => exact ⟨rfl, rfl⟩
  | some framed => exact ⟨rfl, rfl⟩

theorem bracket_stopServingOn :
    Bracket (ServedAgreement.stopServingOn
      (τ := (DigestTape.Record × DigestTape.Record) × Nat)) :=
  fun _ => ⟨rfl, rfl⟩

/-! ## And it is a bracketed recorder run

By `rfl`: the tail was written to the predicate. -/

/-- **The tail is a bracketed recorder run.** -/
theorem isBracketedRecorderRun (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) :
    IsBracketedRecorderRun (ω := Multiplicative Tally) (handlerAt rightKeep)
      (carrierTail rightKeep) adversary :=
  fun walk _ =>
    ⟨SecretKey × PublicKey, Forgery, Bool × Tally,
      Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2,
      fun keys => adversary.main keys.2,
      fun keys => recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1),
      fun keys forgery => countRecorded verifierCost
        (Scheme.verify keys.2 forgery.message forgery.signature),
      ServedAgreement.startServingOn, ServedAgreement.stopServingOn,
      (startAt walk.2, (([], []), 0)),
      fun _ forgery tally log verified state =>
        (({ forgery := forgery
            signed := log
            verified := verified.1
            counts := (Multiplicative.toAdd tally).1 + verified.2.1 },
          (Multiplicative.toAdd tally).2 + verified.2.2), state.2.2),
      rfl, bracket_startServingOn, bracket_stopServingOn, rfl⟩

/-! ## What one stage forgets to

The tail's first and third stages run under the handler directly, and this is what each of them
projects to: the same computation under the shared oracle, counted by `countAllHashes`, with the
handler's counter carried in from where the previous stage left it.

That the starting counter appears on the right is the whole reason `run_withCount_count` was
stated with it rather than at zero. The first stage starts at zero, the second where the first
stopped, the third where the second did — and the three add up only because each equation says
what it started from. -/

/-- **A stage under the handler is the same computation under the shared oracle.** -/
theorem stage_forget (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α) (state : CountedState) :
    (fun z : α × CountedState => ((z.1, z.2.2.2), z.2.1.cache)) <$>
        (simulateQ (handlerAt rightKeep walk) computation).run state =
      (fun r : (α × Nat) × QueryCache HashSpec => ((r.1.1, state.2.2 + r.1.2), r.2)) <$>
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run state.1.cache :=
  CountedHandler.run_withCount_count
    (@noticingRecorderOf HandlerCarrier.State (servingView (keyAt walk))
      (disclosingKeep (keyAt walk)) (rightKeep walk))
    KeygenUniform.rom (CarrierFiles.forgetsAlong_carrierRecorder (keyAt walk) (rightKeep walk))
    computation state

/-! ## The middle stage's projection keeps the count

`stage_forget` is enough for the stages that run under the handler directly. The fused stage is
projected by `ServingForget.run_fuseServing_map`, which needs the handler to forget along the
same map the brackets preserve — and that map has to keep the **count** as well as the cache,
because the count is what the middle stage contributes to the tail's value. So the handler on
the far side is `CountedHandler.romWithCount`, and this is the law. -/

theorem handlerAt_step_forget (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (queried : OracleWorld.Domain) (state : CountedState) :
    (fun z : OracleWorld.Range queried × CountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        ((handlerAt rightKeep walk) queried).run state =
      (CountedHandler.romWithCount queried).run (state.1.cache, state.2.2) := by
  rw [handlerAt, CarrierFiles.countedCarrierRecorder, CountedHandler.withCount_run,
    CountedHandler.romWithCount_run, map_eq_bind_pure_comp, bind_assoc]
  show _ = (KeygenUniform.rom queried).run
      (CacheView.cacheOf (σ := HandlerCarrier.State) (state.1, state.2.1).1) >>= _
  rw [← CarrierFiles.noticingRecorderOf_forget_step (keyAt walk) (rightKeep walk) queried
      (state.1, state.2.1), map_eq_bind_pure_comp, bind_assoc]
  refine bind_congr fun step => ?_
  simp only [Function.comp_def, pure_bind]
  rfl

theorem forgetsAlong_counted (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) :
    ServingForget.ForgetsAlong (fun state : CountedState => (state.1.cache, state.2.2))
      (handlerAt rightKeep walk) CountedHandler.romWithCount := by
  intro β computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind queried next ih =>
    intro state
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind,
      ← handlerAt_step_forget rightKeep walk queried state, bind_map_left]
    exact bind_congr fun step => ih step.1 step.2

/-- **The brackets keep the cache and the count**, which is the projection the middle stage is
read through. `BracketedRun.Bracket` asks for the cache and the recordings; this asks for the
cache and the count, and both hold for the same reason — the brackets write the framing and
nothing else. -/
theorem startServingOn_cacheCount (request : Message) (state : CountedState) :
    ((ServedAgreement.startServingOn request state).1.cache,
        (ServedAgreement.startServingOn request state).2.2) =
      (state.1.cache, state.2.2) := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => rfl
  | some framed => rfl

theorem stopServingOn_cacheCount (state : CountedState) :
    ((ServedAgreement.stopServingOn state).1.cache,
      (ServedAgreement.stopServingOn (τ := (DigestTape.Record × DigestTape.Record) × Nat)
        state).2.2) = (state.1.cache, state.2.2) := rfl

/-- **The middle stage, projected.** The bracketed fused phase over the carrier's handler is the
unbracketed fused phase over the shared oracle with a counter — which is the form
`PhaseFusion.run_phase_fused` turns back into the nested run `RecordedTail.recordedAfterSeeds`
is written as. -/
theorem middle_forget {α : Type} (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (log : SigningLog) (state : CountedState) :
    (fun step : α × (Multiplicative Tally × SigningLog × CountedState) =>
        (step.1, (step.2.1, step.2.2.1, (step.2.2.2.1.cache, step.2.2.2.2.2)))) <$>
      (simulateQ (fuseServing (handlerAt rightKeep walk) inner
        ServedAgreement.startServingOn ServedAgreement.stopServingOn) computation).run
        (accumulated, log, state) =
      (simulateQ (fuse CountedHandler.romWithCount inner) computation).run
        (accumulated, log, (state.1.cache, state.2.2)) :=
  ServingForget.run_fuseServing_map (fun s : CountedState => (s.1.cache, s.2.2))
    (handlerAt rightKeep walk) CountedHandler.romWithCount inner
    ServedAgreement.startServingOn ServedAgreement.stopServingOn startServingOn_cacheCount
    stopServingOn_cacheCount (forgetsAlong_counted rightKeep walk) computation accumulated log
    state

/-! ## The assembly

Both sides are now runs of a counted handler over the same three stages, which is what makes the
composition a composition. `recordedTail_eq_counted` puts the recorded tail at
`CountedHandler.romWithCount` — the count moves from `countAllHashes`, wrapped around the
computation, into the handler's own state, which is where the carrier tail keeps it. After that
the two sides differ only in the handler, and the three stages are matched by the two laws
already proved. -/

set_option maxHeartbeats 1000000 in
/-- **The recorded game splits at its three sequencing points**, under any handler. This is
`FusedGame.run_afterSeeds_split` at the game that keeps the record, and like it the split is the
definition read out: `simulateQ` distributes over the `do` block's binds and `StateT.run`
distributes over those. -/
theorem run_recordedAfterSeeds_split {S : Type}
    (outer : QueryImpl OracleWorld (StateT S ProbComp)) (adversary : Adversary)
    (sds : Digest × Digest × Digest) (state : S) :
    (simulateQ outer (RecordedTail.recordedAfterSeeds adversary sds)).run state =
      (simulateQ outer (Scheme.keygenInternal sds.1 sds.2.1 sds.2.2)).run state >>= fun keys =>
        (simulateQ outer ((((simulateQ (recordedAdversaryImpl +
              recordedSigningOracle (Scheme.sign keys.1.1)) (adversary.main keys.1.2)).run).run
            []))).run keys.2 >>= fun phase =>
          (simulateQ outer (countRecorded verifierCost (Scheme.verify keys.1.2
              phase.1.1.1.message phase.1.1.1.signature))).run phase.2 >>= fun verified =>
            (pure (({
                forgery := phase.1.1.1
                signed := phase.1.2
                verified := verified.1.1
                counts := (Multiplicative.toAdd phase.1.1.2).1 + verified.1.2.1 },
              (Multiplicative.toAdd phase.1.1.2).2 + verified.1.2.2), verified.2) :
              ProbComp ((Outcome × Multiset Bytes) × S)) := by
  unfold RecordedTail.recordedAfterSeeds
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]

attribute [local irreducible] RecordedTail.recordedAfterSeeds Scheme.keygenInternal
  Scheme.verify Scheme.sign Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **The recorded tail is a counted run of the shared oracle.** Nothing changes but where the
count is kept: `countAllHashes` wraps the computation, the counted handler carries it in the
state, and `run_romWithCount_count` says the two agree. -/
theorem recordedTail_eq_counted (adversary : Adversary) (walk : Walk) :
    RecordedTail.recordedTail adversary walk =
      (fun z : (Outcome × Multiset Bytes) × (QueryCache HashSpec × Nat) =>
          ((z.1, z.2.2), z.2.1)) <$>
        (simulateQ CountedHandler.romWithCount
          (RecordedTail.recordedAfterSeeds adversary walk.1.1)).run (walk.2, 0) := by
  rw [RecordedTail.recordedTail,
    CountedHandler.run_romWithCount_count
      (RecordedTail.recordedAfterSeeds adversary walk.1.1) (walk.2, 0),
    show (fun r : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec =>
        ((r.1.1, 0 + r.1.2), r.2)) = id from funext fun r => by rw [Nat.zero_add]; rfl,
    id_map]

/-- The first stage's projection, with the start spelled out so that it matches syntactically.
The projection in `ForgetsAlong` is applied as a lambda, so an instance of it has to be given a
name before `rw` can see through it — the projection trap, at a redex rather than a
metavariable. -/
theorem first_stage_forget (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α) :
    (fun z : α × CountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        (simulateQ (handlerAt rightKeep walk) computation).run
          (startAt walk.2, (([], []), 0)) =
      (simulateQ CountedHandler.romWithCount computation).run (walk.2, 0) :=
  forgetsAlong_counted rightKeep walk computation (startAt walk.2, (([], []), 0))

set_option maxHeartbeats 1000000 in
/-- The middle stage's projection, named at the state it is used at. Same reason as
`first_stage_forget`, one step later: `PhaseFusion.run_phase_fused`'s writer and state are
determined only once the previous stage's rewrite has landed, so a rewrite that has to find them
has nothing to find. Naming the instance costs three lines. -/
theorem middle_stage_forget (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (adversary : Adversary)
    (keys : (SecretKey × PublicKey) × CountedState) :
    (simulateQ CountedHandler.romWithCount
        (((simulateQ (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          (adversary.main keys.1.2)).run).run [])).run (keys.2.1.cache, keys.2.2.2) =
      (fun step : Forgery × (Multiplicative Tally × SigningLog × CountedState) =>
          (((step.1, step.2.1), step.2.2.1), (step.2.2.2.1.cache, step.2.2.2.2.2))) <$>
        (simulateQ (fuseServing (handlerAt rightKeep walk)
          (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
          ServedAgreement.startServingOn ServedAgreement.stopServingOn)
          (adversary.main keys.1.2)).run (1, [], keys.2) := by
  rw [PhaseFusion.run_phase_fused CountedHandler.romWithCount
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) [] (keys.2.1.cache, keys.2.2.2),
    ← middle_forget rightKeep walk
      (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
      (adversary.main keys.1.2) 1 [] keys.2, Functor.map_map]

set_option maxHeartbeats 1000000 in
/-- The third stage's projection, named the same way. -/
theorem last_stage_forget (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (pk : PublicKey) (forgery : Forgery) (state : CountedState) :
    (fun z : (Bool × Tally) × CountedState => (z.1, (z.2.1.cache, z.2.2.2))) <$>
        (simulateQ (handlerAt rightKeep walk) (countRecorded verifierCost
          (Scheme.verify pk forgery.message forgery.signature))).run state =
      (simulateQ CountedHandler.romWithCount (countRecorded verifierCost
        (Scheme.verify pk forgery.message forgery.signature))).run
        (state.1.cache, state.2.2) :=
  forgetsAlong_counted rightKeep walk
    (countRecorded verifierCost (Scheme.verify pk forgery.message forgery.signature)) state

/-! ## What is left, and it is no longer an argument

`forget_carrierTail` — that the mapped tail is `RecordedTail.recordedTail` — is the three stages
put together, and all three are now named at the states they are used at:
`first_stage_forget`, `middle_stage_forget`, `last_stage_forget`. Each is the projection law at
one stage with nothing left for a rewrite to find, which was the difficulty the previous pass
diagnosed.

What remains is bookkeeping of a kind worth naming because it is where the next pass will go:
the two sides normalise their `map`s over `bind`s in different orders, so the chain of
`map_bind`, `bind_map_left` and `bind_congr` has to be driven rather than let run. A `conv` at
each side, or a `simp only` with the three stage lemmas and the map laws, will do it; what will
not is a flat `rw` list, because the same `map_bind` matches on either side and the first match
wins.

Everything the composition needs is proved. Nothing in it is an argument. -/


end SlhDsaSecurity.CarrierTail

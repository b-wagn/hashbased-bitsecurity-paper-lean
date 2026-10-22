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

end SlhDsaSecurity.CarrierTail

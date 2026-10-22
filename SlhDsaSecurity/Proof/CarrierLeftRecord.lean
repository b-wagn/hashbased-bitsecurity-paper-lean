import SlhDsaSecurity.Proof.CarrierRecordings
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.RecordInvariant

/-!
# What the disclosing recording holds

The served-agreement hypothesis says every entry of the **disclosing** recording is in the
signed log. `CarrierRecordings` reads the target recording and not this one, so the first half
has to be read here: an entry reaches the disclosing recording only by passing
`CarriedWitness.disclosingKeep`, which is `HandlerCarrier.FilesLeft` — *there is a request in
flight and the input is that request's message input.*

So every disclosing entry carries a **frame**, and its input is that frame's message input at
some randomiser. That is what this file proves, at the carrier tail, with no hypothesis.

**It is the shape half, and the other half is not here.** Knowing the entry names a frame that
was in flight is not yet knowing that frame was *logged with a signature carrying that
randomiser*, which is what `ServedLog.servedLog` asks. That second half is the carrier-to-log
agreement — `ServedBridge.ServedAgree`'s `CarrierBelowLog` — and the route to it is named at the
end of this file rather than guessed at here.

## How it is proved

As an invariant rather than a suffix. `CarrierRecordings.run_right_suffix` hands back, per
entry, the state it was filed at, because its consumers need the *cache* in force there. Nothing
here does: `FilesLeft` reads the framing alone, and the conclusion existentially quantifies the
view, so what survives a step survives the run. That makes it a `RecordInvariant` client, and
the brackets are free — `BracketedRun.Bracket` fixes the recordings outright.

**A relation would have been the wrong choice here, and a predicate is right**, which is worth
saying next to the opposite call made for `SplitCounted.Tracks`: that one compared a run's two
ends, so it had to be a relation; this one is a property of one state that every step preserves,
so a predicate composes by itself.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierLeftRecord

open Security RecorderView HandlerCarrier CarriedWitness PhaseFusion RecordedQueries
open BracketedRun CarrierTail

variable (pk : PublicKey)

open scoped Classical in
/-- **A step appends at most its own query's entry to the disclosing recording**, and when it
does, the left test held at the state the notice had reached — which is `FilesLeft` at that
view. -/
theorem step_left_mem (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support
      (((CarrierFiles.countedCarrierRecorder pk rightKeep) queried).run state))
    (entry : Bytes × HashOutput) (hentry : entry ∈ step.2.2.1.1) :
    entry ∈ state.2.1.1 ∨
      ∃ view : HandlerCarrier.State, HandlerCarrier.FilesLeft pk view entry.1 := by
  classical
  obtain ⟨inner, hinner, hvalue, -, hcarried⟩ :=
    CountedHandler.withCount_step _ queried state step hstep
  rw [hcarried] at hentry
  rcases queried with coin | input
  · rw [show inner.2.2 = (state.1, state.2.1).2 from
      congrArg Prod.snd (@recorderOf_step_inl HandlerCarrier.State (servingView pk)
        (disclosingKeep pk) rightKeep coin (state.1, state.2.1) inner
        (by rw [← @noticingRecorderOf_run_inl HandlerCarrier.State (servingView pk)]
            exact hinner))] at hentry
    exact Or.inl hentry
  · have hinr := hinner
    rw [@noticingRecorderOf_run_inr HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input (state.1, state.2.1)] at hinr
    rw [@recorderOf_step_record HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner hinr] at hentry
    rcases @appendedOf_left_mem HandlerCarrier.State (servingView pk) (disclosingKeep pk)
      rightKeep input _ inner.1 entry hentry with hprior | ⟨hself, -, hleft⟩
    · exact Or.inl hprior
    · refine Or.inr ⟨servingNotice pk state.1 input, ?_⟩
      rw [show entry.1 = input from by rw [hself]]
      exact hleft

/-- **Every disclosing entry carries a frame.** The invariant the three stages compose along. -/
def LeftFramed (state : CountedState) : Prop :=
  ∀ entry ∈ state.2.1.1, ∃ view : HandlerCarrier.State, HandlerCarrier.FilesLeft pk view entry.1

theorem leftFramed_start (cache : QueryCache HashSpec) :
    LeftFramed pk (startAt cache, (([], []), 0)) := by
  intro entry hentry
  exact absurd hentry (by simp)

theorem step_leftFramed (rightKeep : Bytes → HandlerCarrier.State → Prop)
    (queried : OracleWorld.Domain) (state : CountedState)
    (step : OracleWorld.Range queried × CountedState)
    (hstep : step ∈ support
      (((CarrierFiles.countedCarrierRecorder pk rightKeep) queried).run state))
    (hinv : LeftFramed pk state) : LeftFramed pk step.2 := fun entry hentry =>
  (step_left_mem pk rightKeep queried state step hstep entry hentry).elim (hinv entry) id

/-- **The brackets keep it**, because `BracketedRun.Bracket` fixes both recordings. -/
theorem leftFramed_startServingOn (request : Message) (state : CountedState)
    (hinv : LeftFramed pk state) :
    LeftFramed pk (ServedAgreement.startServingOn request state) := by
  rw [ServedAgreement.startServingOn]
  cases request.frame with
  | none => exact hinv
  | some framed => exact hinv

theorem leftFramed_stopServingOn (state : CountedState) (hinv : LeftFramed pk state) :
    LeftFramed pk (ServedAgreement.stopServingOn state) := hinv

set_option maxHeartbeats 1000000 in
/-- **And so every disclosing entry of the carrier tail names a frame**, with no hypothesis.
Three stages, two of them `RecordInvariant.run_invariant` and the middle
`RecordInvariant.phase_invariant`. -/
theorem leftFramed_carrierTail (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (adversary : Adversary) (walk : Walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk)) :
    ∀ entry ∈ result.2.2.1, ∃ (randomizer : Digest) (framed : Bytes),
      entry.1 = Hashing.messageInput randomizer (keyAt walk) framed := by
  classical
  rw [carrierTail, mem_support_bind_iff] at hresult
  obtain ⟨keys, hkeys, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨middle, hmiddle, hrest⟩ := hrest
  rw [mem_support_bind_iff] at hrest
  obtain ⟨final, hlast, hpure⟩ := hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  have hfirst := RecordInvariant.run_invariant (Inv := LeftFramed (keyAt walk)) _
    (fun queried state step hstep hinv =>
      step_leftFramed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    _ (startAt walk.2, (([], []), 0)) keys hkeys (leftFramed_start (keyAt walk) walk.2)
  have hsecond := RecordInvariant.phase_invariant (Inv := LeftFramed (keyAt walk)) _
    (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1.1))
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    (fun queried state step hstep hinv =>
      step_leftFramed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    (fun request state hinv => leftFramed_startServingOn (keyAt walk) request state hinv)
    (fun state hinv => leftFramed_stopServingOn (keyAt walk) state hinv)
    _ 1 [] keys.2 middle hmiddle hfirst
  have hthird := RecordInvariant.run_invariant (Inv := LeftFramed (keyAt walk)) _
    (fun queried state step hstep hinv =>
      step_leftFramed (keyAt walk) (rightKeep walk) queried state step hstep hinv)
    _ middle.2.2.2 final hlast hsecond
  intro entry hentry
  rw [hpure] at hentry
  obtain ⟨view, framed, -, randomizer, hinput⟩ := hthird entry hentry
  exact ⟨randomizer, framed, hinput⟩

/-! ## What is left, and where it lives

`ServedLog.servedLog` asks more than a frame: it asks that the frame appear in the run's
**signed log**, with an answer that parses, and with the parsed signature's randomiser equal to
the one in the entry. Two things connect the frame to the log, and both already exist:

* `CarriedWitness.served_servingNotice_self` — an input the carrier files left is in the
  carrier's served set from that step on, which with `HandlerCarrier.Grows` reaches the tail's
  final carrier;
* `ServedBridge.ServedAgree`'s `CarrierBelowLog` — the carrier's served set is below the log's.

So the remaining obligation is `Served → servedLog`, and it has no recorder in it. It is not
proved here because the carrier the tail ends at is dropped by `BracketedRun.forgetCarrier`,
so the statement has to be made before the projection, where `ServedAgreement`'s own run laws
already live. -/

end SlhDsaSecurity.CarrierLeftRecord

import SlhDsaSecurity.Proof.ServingProgram
import SlhDsaSecurity.Proof.PhaseFusion
import SlhDsaSecurity.Proof.RecordedQueries

/-!
# The brackets: the signing oracle setting and clearing the framing

`PhaseFusion.fuse` made a signing request **one step**, with the handler's state in hand on both
sides of the signer's sub-run. `ServingProgram` made a handler that files what it recognises.
This file puts them together: the fused phase, with the signing step bracketed by
`HandlerCarrier.setFraming` and `clearFraming`, so that the signer's own queries — and only the
signer's — run with a framing set.

**The invariant is the point, and it is carried as a fact about the run.** That "only the signing
oracle sets the framing" is visible in the definition proves nothing about what happens when the
adversary asks. `framing_clear_run` is the fact: starting from a cleared state, the framing is
clear at every step boundary, so every query of the adversary's is answered with it clear. With
`HandlerCarrier.not_filesLeft_of_clear` that gives `not_filesLeft_adversary` — nothing the
adversary asks is ever filed — which is the property the whole served notion rests on and the one
the cache proxy could not have.

The two halves of the invariant are different in kind and both are needed. Inside a signing step
the framing is set and then cleared, so the step *restores* it; outside one the handler never
writes it, which is `ServingProgram.servingProgram_run_framing`. Neither alone says what happens
at an adversary query that follows a signature.

**What this presentation exposes, for the consumer that will want it.** The fused state is
`Multiplicative RecordedQueries.Tally × SigningLog × OpenCache.HandlerState`, so a run of it
carries *both* recordings — the writer's `Tally`, which is the adversary's and the verifier's
record, and the handler's own probe list inside `HandlerState` — together with the log and the
carrier. Anything downstream that needs the two recordings rather than one record can read them
off this state without a further presentation.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ServingPhase

open Security OpenCache CanonicalGraph RecordedQueries ServingProgram

variable (publicSeed : Digest)

/-! ## The brackets -/

/-- Set the framing a request names, when it has one. A request with no frame is rejected before
any query, so there is nothing to serve and nothing to set. -/
def startServing (request : Message) (state : HandlerState) : HandlerState :=
  match request.frame with
  | none => state
  | some framed => (HandlerCarrier.setFraming state.1 framed, state.2)

/-- Clear it when the request returns. -/
def stopServing (state : HandlerState) : HandlerState :=
  (HandlerCarrier.clearFraming state.1, state.2)

@[simp] theorem framing_stopServing (state : HandlerState) :
    (stopServing state).1.framing = none := rfl

/-- The phase: the adversary and the signer under one handler, with the signing step bracketed
so that the signer's sub-run is the only thing that runs with a framing set. -/
noncomputable def servingPhase (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT (Multiplicative Tally × SigningLog × HandlerState) ProbComp) :=
  PhaseFusion.fuseServing (servingProgram publicSeed pk availableAt table)
    (recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
    startServing stopServing

/-! ## The invariant -/

open scoped Classical in
/-- **A step of the phase leaves the framing clear.** At a signing request the bracket clears it;
at anything else the handler never wrote it. -/
theorem framing_clear_step (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (hclear : state.2.2.1.framing = none)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × HandlerState))
    (hstep : step ∈ support (((servingPhase publicSeed pk availableAt table sk) queried).run
      state)) : step.2.2.2.1.framing = none := by
  classical
  rcases queried with world | request
  · -- The adversary's own query: the handler does not write the framing.
    have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedAdversaryImpl world).run).run state.2.1)).run state.2.2 >>=
          fun inner =>
            (pure (inner.1.1.1, (state.1 * inner.1.1.2, inner.1.2, inner.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, hinner, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = inner.2 from by rw [hpure],
      servingProgram_run_framing publicSeed pk availableAt table _ state.2.2 inner hinner]
    exact hclear
  · -- A signing request: the bracket clears it, whatever the sub-run did.
    have hrun : step ∈ support
        ((simulateQ (servingProgram publicSeed pk availableAt table)
          (((recordedSigningOracle (Scheme.sign sk) request).run).run state.2.1)).run
            (startServing request state.2.2) >>= fun inner =>
          (pure (inner.1.1.1,
            (state.1 * inner.1.1.2, inner.1.2, stopServing inner.2)) :
            ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
              (Multiplicative Tally × SigningLog × HandlerState)))) := hstep
    rw [mem_support_bind_iff] at hrun
    obtain ⟨inner, -, hpure⟩ := hrun
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.2.2 = stopServing inner.2 from by rw [hpure]]
    exact framing_stopServing inner.2

open scoped Classical in
/-- **The framing is clear at every step boundary of a run.** The fact the adversary's blindness
is read against. -/
theorem framing_clear_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (state : Multiplicative Tally × SigningLog × HandlerState),
      state.2.2.1.framing = none →
      ∀ z ∈ support ((simulateQ (servingPhase publicSeed pk availableAt table sk)
        computation).run state), z.2.2.2.1.framing = none := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hclear z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact hclear
  | query_bind queried next ih =>
    intro state hclear z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact ih step.1 step.2
      (framing_clear_step publicSeed pk availableAt table sk queried state hclear step hstep)
      z hrest

/-! ## What the invariant buys -/

/-- **Nothing the adversary asks is ever filed.** Its queries run at a step boundary, where the
framing is clear, and a clear framing files nothing whatever the input is. -/
theorem not_filesLeft_adversary (pk : PublicKey)
    (state : Multiplicative Tally × SigningLog × HandlerState)
    (hclear : state.2.2.1.framing = none) (input : Bytes) :
    ¬ HandlerCarrier.FilesLeft pk state.2.2.1 input :=
  HandlerCarrier.not_filesLeft_of_clear pk state.2.2.1 hclear input

/-! ## The other half, and what it retires

The ordering defect needs one fact beyond the blindness above: **no target-recorded input is a
served request's own digest input.** At a cache-readable disclosing test that fact is an ordering
statement — the signer asks for its randomiser before its digest, so the randomiser's answer is
cached by the time the digest query is made — and nothing reports what the cache holds partway
through a sub-run, which is why it has stood as a hypothesis.

At the carrier's test there is no ordering to establish and no cache to consult. The bracket sets
the framing before the sub-run, `servingProgram_framing` never writes it, and the signer's digest
input is `Hashing.messageInput _ pk message` for the very `message` the framing names, by
`HonestProbes.probes_sign`. So the test holds at the state the query is made from, for the
state's own reason. -/

theorem framing_startServing (request : Message) (message : Bytes)
    (hframe : request.frame = some message) (state : HandlerState) :
    (startServing request state).1.framing = some message := by
  rw [startServing, hframe]
  exact HandlerCarrier.framing_setFraming state.1 message

open scoped Classical in
/-- **The framing stays the request's own for the whole of the signer's sub-run**, so it names
that request at every query the signer makes, not only at the two ends. -/
theorem framing_serving_run (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (request : Message) (message : Bytes) (hframe : request.frame = some message)
    {α : Type} (computation : OracleComp OracleWorld α) (state : HandlerState)
    (z : α × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run (startServing request state))) :
    z.2.1.framing = some message := by
  rw [servingProgram_run_framing publicSeed pk availableAt table computation
    (startServing request state) z hz]
  exact framing_startServing request message hframe state

/-- **The signer's own digest query meets the carrier's left test at the state it is made from.**
The flag is the whole of it: the input's shape comes from the request the framing names, and no
entry of the cache is read. This is the fact the ordering defect's remaining hypothesis asks
for, with the ordering gone. -/
theorem filesLeft_signer_digest (pk : PublicKey)
    (availableAt : HandlerCarrier.State → Node → Prop) (table : Cells × Padding)
    (request : Message) (message : Bytes) (hframe : request.frame = some message)
    {α : Type} (computation : OracleComp OracleWorld α) (state : HandlerState)
    (z : α × HandlerState)
    (hz : z ∈ support ((simulateQ (servingProgram publicSeed pk availableAt table)
      computation).run (startServing request state)))
    (randomizer : Digest) :
    HandlerCarrier.FilesLeft pk z.2.1 (Hashing.messageInput randomizer pk message) :=
  ⟨message, framing_serving_run publicSeed pk availableAt table request message hframe
    computation state z hz, randomizer, rfl⟩

end SlhDsaSecurity.ServingPhase

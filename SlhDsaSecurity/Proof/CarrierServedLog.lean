import SlhDsaSecurity.Proof.CarrierCap
import SlhDsaSecurity.Proof.CarrierClearFraming

/-!
# From the carrier's served set to the log, before the projection

The served-agreement hypothesis needs `HandlerCarrier.Served → ServedLog.servedLog`, and
`ServedBridge.CarrierBelowLog` is that statement. It has to be made **before**
`BracketedRun.forgetCarrier`, which drops the carrier the tail ends at — so it is not a fact
about a supported result of `CarrierTail.carrierTail`, and trying to phrase it as one is how a
lemma ends up at a presentation nobody can use.

`ServedAgreement.carrierLogged_run_with` is the engine and is already general in the start
state: it asks for nothing in flight and `CarrierLogged` there. What was missing was the two
ends of the tail.

**At the front**, `carrierLogged_empty` is the vacuous instance at `HandlerCarrier.empty`, and
the tail does not start there — it starts after key generation, at a carrier with a warm cache.
What makes the instance vacuous is not emptiness but an **empty served set**, so the general
form is `carrierLogged_of_served_zero`, and `CarrierCap.quiet_run` already delivers its
hypothesis across key generation.

**At the back**, the verifier's stage runs after the phase, when the served set is no longer
empty, so `Quiet` does not survive it and nothing weaker was stated. What is true is that the
stage files nothing, because `CarrierClearFraming` enters it with nothing in flight and
`HandlerCarrier.FilesLeft` cannot match a clear frame — so the served set comes out of it
**unchanged**, whatever it was. That is `served_run_of_clear`, and it is `CarrierCap.quiet_run`'s
argument with the served set a parameter instead of zero.

Both are the same observation read at the two ends: *filing needs a frame in flight, and both
of the tail's unbracketed stages have none.*
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierServedLog

open Security BracketedRun CarrierFiles CarrierTail PhaseFusion RecordInvariant
open RecordedQueries RecorderView CarriedWitness HandlerCarrier

/-- **A carrier that has served nothing is logged, vacuously.**
`ServedAgreement.carrierLogged_empty` is this at `HandlerCarrier.empty`; what the argument
actually uses is the empty served set, and the tail needs it at a carrier with a warm cache. -/
theorem carrierLogged_of_served_zero (sk : SecretKey) (warm : QueryCache HashSpec)
    (log : SigningLog) (carrier : HandlerCarrier.State) (hserved : carrier.served = 0) :
    ServedAgreement.CarrierLogged sk warm log carrier := by
  intro _ _ _ input hservedAt
  rw [HandlerCarrier.Served, hserved] at hservedAt
  exact absurd hservedAt (by simp)

/-- The invariant the verifier's stage keeps: nothing in flight, and the served set it was
entered with. -/
def ClearWith (served : Multiset Bytes) (carrier : HandlerCarrier.State) : Prop :=
  carrier.framing = none ∧ carrier.served = served

theorem clearWith_cacheAnswer (served : Multiset Bytes) (carrier : HandlerCarrier.State)
    (input : Bytes) (answer : HashOutput) (hinv : ClearWith served carrier) :
    ClearWith served (HandlerCarrier.cacheAnswer carrier input answer) :=
  ⟨by rw [HandlerCarrier.framing_cacheAnswer]; exact hinv.1,
    by rw [HandlerCarrier.served_cacheAnswer]; exact hinv.2⟩

/-- **A run under the tail's handler with nothing in flight serves nothing new.**
`CarrierCap.quiet_run` with the served set a parameter instead of zero: the filing clause is
refuted by the clear frame either way, and only the `Quiet` version needed it to be zero. -/
theorem clearWith_run (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    (served : Multiset Bytes) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support
      ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hinv : ClearWith served state.1) : ClearWith served result.2.1 :=
  (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)).invariant (ClearWith served)
    (clearWith_cacheAnswer served)
    (fun carrier input hcarrier hfiles =>
      absurd hfiles (HandlerCarrier.not_filesLeft_of_clear (keyAt walk) carrier hcarrier.1 input))
    computation state result hresult hinv

/-- **So the verifier's stage leaves the served set where the phase left it.** -/
theorem served_run_of_clear (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none) : result.2.1.served = state.1.served :=
  (clearWith_run rightKeep walk state.1.served computation state result hresult
    ⟨hclear, rfl⟩).2

/-- **And a carrier that served nothing before the stage serves nothing after it**, which is
the front end read the same way. -/
theorem carrierLogged_run_of_clear (sk : SecretKey) (warm : QueryCache HashSpec)
    (log : SigningLog) (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hquiet : CarrierCap.Quiet state.1) :
    ServedAgreement.CarrierLogged sk warm log result.2.1 :=
  carrierLogged_of_served_zero sk warm log result.2.1
    (CarrierCap.quiet_run rightKeep walk computation state result hresult hquiet).2

/-! ## What the middle stage then needs

With both ends in hand the remaining step is one application of
`ServedAgreement.carrierLogged_run_with` at the tail's middle stage, whose hypotheses are about
the **signer** and not about the carrier: `SignerShape sk (Scheme.sign sk)`,
`SignerPins sk warm (Scheme.sign sk)` at the warm cache the walk supplies, and `sk.publicKey =
pk`. `ServedAgreement.servedAgree_run` discharges exactly those at the serving phase's own
handler, so what is left is to re-point them at `CarrierTail.handlerAt` — which
`carrierLogged_run_with` already allows, being generic in the handler and its `Files` instance.

`ServedAgreement.servedLog_iff_logServed` then turns `logServed` into `ServedLog.servedLog`,
which is `ServedBridge.CarrierBelowLog` and the half of the served-agreement hypothesis that
`CarrierLeftRecord` left open. -/

end SlhDsaSecurity.CarrierServedLog

import SlhDsaSecurity.Proof.CarrierCap
import SlhDsaSecurity.Proof.CarrierClearFraming
import SlhDsaSecurity.Proof.CarrierCover

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

/-! ## The middle stage, applied

The hypotheses `ServedAgreement.carrierLogged_run_with` asks for are about the **signer**, and
`servedAgree_run` states which cache it means them at: it passes `warm := fun _ => none`, with
`signerPins_sign`'s own docstring saying why — *nothing is stripped, so the pin holds at every
cache and the table is empty.* So there was nothing to decide here, only something to read.

`ServedAgreement.servingPhaseWith impl signer` is `fuseServing impl (recordedAdversaryImpl +
recordedSigningOracle signer) startServingOn stopServingOn`, which is the carrier tail's middle
stage on the nose. -/

/-- **The middle stage leaves the carrier logged.** -/
theorem carrierLogged_phase (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (sk : SecretKey) (hpk : sk.publicKey = keyAt walk)
    (hpublic : ¬ HashSeparation.Possible (sk.publicKey.seed, sk.publicKey.root))
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (state : CountedState)
    (hclear : state.1.framing = none) (hserved : state.1.served = 0)
    (z : α × (Multiplicative Tally × SigningLog × CountedState))
    (hz : z ∈ support ((simulateQ (ServedAgreement.servingPhaseWith (handlerAt rightKeep walk)
      (Scheme.sign sk)) phase).run (accumulated, [], state))) :
    ServedAgreement.CarrierLogged sk (fun _ => none) z.2.2.1 z.2.2.2.1 :=
  ServedAgreement.carrierLogged_run_with (keyAt walk) (handlerAt rightKeep walk)
    (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
    (ServedAgreement.signerShape_sign sk) (fun _ => none)
    (ServedAgreement.signerPins_sign sk hpublic) phase (accumulated, [], state) hclear
    (carrierLogged_of_served_zero sk (fun _ => none) [] state.1 hserved) z hz

/-! ## And it survives the verifier's stage

`CarrierLogged` reads two things of the carrier: the caches that extend it, and what it has
served. The verifier's stage only grows the first and, entered with nothing in flight, leaves
the second alone — so both halves of the transfer are already proved above and in
`CarrierCover`. -/

/-- **A stage under the tail's handler only grows the cache.** -/
theorem cache_persists_run (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (input : Bytes) (value : HashOutput) (hentry : state.1.cache input = some value) :
    result.2.1.cache input = some value := by
  letI : RecorderView.CacheView HandlerCarrier.State := servingView (keyAt walk)
  exact NoticingCover.cache_value_persists (disclosingKeep (keyAt walk)) (rightKeep walk)
    computation (CarrierCover.dropCount state) (result.1, CarrierCover.dropCount result.2)
    (CarrierCover.mem_support_dropCount_run (keyAt walk) (rightKeep walk) computation state
      result hresult) input value hentry

/-- **So a logged carrier stays logged across it.** -/
theorem carrierLogged_run (sk : SecretKey) (warm : QueryCache HashSpec) (log : SigningLog)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none)
    (hlogged : ServedAgreement.CarrierLogged sk warm log state.1) :
    ServedAgreement.CarrierLogged sk warm log result.2.1 := by
  intro later hlater hwarm input hserved
  refine hlogged later
    (fun probe value hvalue => hlater probe value
      (cache_persists_run rightKeep walk computation state result hresult probe value hvalue))
    hwarm input ?_
  rw [HandlerCarrier.Served,
    served_run_of_clear rightKeep walk computation state result hresult hclear] at hserved
  exact hserved

/-- **A stage with nothing in flight grows the carrier and nothing more.** -/
theorem grows_run_of_clear (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none) : HandlerCarrier.Grows state.1 result.2.1 :=
  ⟨fun input value hvalue =>
      cache_persists_run rightKeep walk computation state result hresult input value hvalue,
    fun input hinput => by
      rw [HandlerCarrier.Served,
        served_run_of_clear rightKeep walk computation state result hresult hclear]
      exact hinput⟩

/-! ## The same application, at the other invariant

`servedLog_iff_logServed` asks for `LogFiled` where `carrierLogged_run_with` asked for
`CarrierLogged`, and `logFiled_run_with` is the mirror law — generic in the handler and its
`Files` instance in exactly the same way, started by `logFiled_nil`, and wanting
`SignerFaithful`, which `signerFaithful_sign` supplies at *any* handler that files. So the
middle stage is one application again, and the verifier's stage is `LogFiled.mono` against the
growth just proved. -/

/-- **The middle stage leaves the log filed.** -/
theorem logFiled_phase (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (walk : Walk) (sk : SecretKey) (hpk : sk.publicKey = keyAt walk)
    {α : Type} (phase : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : Multiplicative Tally) (state : CountedState)
    (z : α × (Multiplicative Tally × SigningLog × CountedState))
    (hz : z ∈ support ((simulateQ (ServedAgreement.servingPhaseWith (handlerAt rightKeep walk)
      (Scheme.sign sk)) phase).run (accumulated, [], state))) :
    ServedAgreement.LogFiled sk z.2.2.1 z.2.2.2.1 :=
  ServedAgreement.logFiled_run_with (keyAt walk) (handlerAt rightKeep walk)
    (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) (Scheme.sign sk) sk hpk
    (ServedAgreement.signerShape_sign sk)
    (ServedAgreement.signerFaithful_sign (keyAt walk) (handlerAt rightKeep walk)
      (files_countedCarrierRecorder (keyAt walk) (rightKeep walk)) sk)
    phase (accumulated, [], state) (ServedAgreement.logFiled_nil sk _) z hz

/-- **And the verifier's stage keeps it.** -/
theorem logFiled_run (sk : SecretKey) (log : SigningLog)
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop) (walk : Walk)
    {α : Type} (computation : OracleComp OracleWorld α)
    (state : CountedState) (result : α × CountedState)
    (hresult : result ∈ support ((simulateQ (handlerAt rightKeep walk) computation).run state))
    (hclear : state.1.framing = none)
    (hfiled : ServedAgreement.LogFiled sk log state.1) :
    ServedAgreement.LogFiled sk log result.2.1 :=
  hfiled.mono (grows_run_of_clear rightKeep walk computation state result hresult hclear)

/-! ## And the containment itself

`ServedBridge.CarrierBelowLog`, at a pre-projection carrier that is logged and a log that is
filed. No recorder, no stages, no run: the two invariants are the whole of it, which is why
they were worth reaching separately. -/

/-- **The carrier's served set is below the log's.** -/
theorem carrierBelowLog_of_invariants (sk : SecretKey) (pk : PublicKey)
    (hpk : sk.publicKey = pk) (log : SigningLog) (carrier : HandlerCarrier.State)
    (hfiled : ServedAgreement.LogFiled sk log carrier)
    (hlogged : ServedAgreement.CarrierLogged sk (fun _ => none) log carrier)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hsigned : result.1.1.signed = log)
    (hcache : ∀ (input : Bytes) (value : HashOutput), carrier.cache input = some value →
      result.2 input = some value) :
    ServedBridge.CarrierBelowLog pk carrier result := by
  intro input hserved
  exact (ServedAgreement.servedLog_iff_logServed sk pk hpk log carrier hfiled result.2 hcache
    result hsigned input).mpr
    (hlogged result.2 hcache (fun _ _ hvalue => absurd hvalue (by simp)) input hserved)

/-! ## What the containment then needs

`carrierBelowLog_of_invariants` is `ServedBridge.CarrierBelowLog` from the two invariants
alone, and both invariants now reach the tail's final pre-projection carrier — the middle stage
by one application each of `carrierLogged_run_with` and `logFiled_run_with`, the verifier's
stage by the growth `grows_run_of_clear` proves.

**What is left is the instantiation at `CarrierTail.carrierTail` itself**: splitting the tail at
its three sequencing points, taking `sk := keys.1.1` with `hpk` from
`CarrierRecord.keys_publicKey` and `hpublic` from `AnswerSide.not_possible_generatedKey` on a
good walk, and feeding `hcache` from the run's own cache. That is bookkeeping over a
decomposition this development has written five times, and it is the only thing between here
and the served-agreement hypothesis. -/

end SlhDsaSecurity.CarrierServedLog

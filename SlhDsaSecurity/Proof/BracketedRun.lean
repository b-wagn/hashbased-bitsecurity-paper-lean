import SlhDsaSecurity.Proof.ServingForget
import SlhDsaSecurity.Proof.LateProbes
import SlhDsaSecurity.Proof.CountedHandler

/-!
# What a bracketed tail is, and why the predicate looks like this

`LateProbes.IsRecorderRun` asks a tail to **be** `simulateQ (recorder …) computation` for some
`computation : OracleComp OracleWorld _`. A carrier tail cannot be: the brackets write the state
between queries, and an `OracleComp OracleWorld` can only sample or query. So the predicate has
to widen, and this is the widening.

**It is three stages, and the three-stage shape is forced by the recording, not by the
plumbing.** `PhaseFusion.fuse`'s `inl` branch runs `inner` before `outer`, and `inner` here is
`recordedAdversaryImpl + recordedSigningOracle` — so lifting key generation into the fused
computation would charge key generation's queries to the adversary's record and count them as
its work. Key generation and verification therefore run under the handler *directly*, and only
the adversary's phase is fused. Anyone later tempted to simplify this back to one run should
read that sentence first: the simplification is not a presentation choice, it changes what the
record holds.

**The brackets' one condition is the lemma's.** For the consumers to survive, the brackets have
to leave the cache alone and leave both recordings alone — and those two are exactly the
hypotheses of `ServingForget.run_fuseServing_map`. `Bracket` is defined to be what that lemma
asks for, and `run_bracketed_map` is the payoff with no extra hypothesis. The predicate's side
conditions and the lemma that discharges them are one text, so they cannot drift.

**The state is the counted one.** A bracketed game is not a single computation, so there is
nothing for `countAllHashes` to wrap and the count lives in the handler's state —
`CountedHandler` says why. That fixes the shape to `HandlerCarrier.State × ((Record × Record) ×
Nat)`: the carrier first, because `ServedAgreement.Files` reads it there; the recordings next,
because the recorder writes them; the count last, because nothing but the value reads it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.BracketedRun

open Security RecorderView PhaseFusion CountedHandler

/-- The walk a tail is read at. -/
abbrev Walk : Type :=
  ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec

/-- The state a counted recorder runs over: carrier, two recordings, count. -/
abbrev CountedState : Type :=
  HandlerCarrier.State × ((DigestTape.Record × DigestTape.Record) × Nat)

variable {ω : Type} [Monoid ω]

/-- **The brackets touch neither the cache nor either recording.** The one condition a bracket
has to meet, and the one `ServingForget.run_fuseServing_map` asks for. -/
def Bracket (f : CountedState → CountedState) : Prop :=
  ∀ state : CountedState, (f state).1.cache = state.1.cache ∧ (f state).2.1 = state.2.1

/-- The projection a bracketed run is read through: the cache and the two recordings. The
carrier's served set and framing go, and so does the count, which the value carries instead. -/
def forgetCarrier (state : CountedState) : SplitPrefix.SplitState :=
  (state.1.cache, state.2.1)

theorem forgetCarrier_of_bracket {f : CountedState → CountedState} (hf : Bracket f)
    (state : CountedState) : forgetCarrier (f state) = forgetCarrier state := by
  rw [forgetCarrier, forgetCarrier, (hf state).1, (hf state).2]

/-- **A bracketed recorder run.** Key generation under the handler, the adversary's phase fused
and bracketed, verification under the handler again, read through the projection. -/
def IsBracketedRecorderRun
    (handler : Walk → QueryImpl OracleWorld (StateT CountedState ProbComp))
    (fused : LateProbes.FusedTail) (adversary : Adversary) : Prop :=
  ∀ walk ∈ support WarmedGame.graphWalk,
    ∃ (β α γ : Type) (first : OracleComp OracleWorld β)
      (phase : β → OracleComp (OracleWorld + SigningSpec) α)
      (inner : β → QueryImpl (OracleWorld + SigningSpec)
        (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
      (last : β → α → OracleComp OracleWorld γ)
      (before : Message → CountedState → CountedState) (after : CountedState → CountedState)
      (start : CountedState)
      (value : β → α → ω → SigningLog → γ → CountedState → (Outcome × Multiset Bytes) × Nat),
      forgetCarrier start = (walk.2, [], []) ∧
        (∀ request : Message, Bracket (before request)) ∧ Bracket after ∧
        fused adversary walk =
          (simulateQ (handler walk) first).run start >>= fun keys =>
            (simulateQ (fuseServing (handler walk) (inner keys.1) before after)
                (phase keys.1)).run ((1 : ω), [], keys.2) >>= fun middle =>
              (simulateQ (handler walk) (last keys.1 middle.1)).run middle.2.2.2 >>=
                fun final =>
                (pure (value keys.1 middle.1 middle.2.1 middle.2.2.1 final.1 final.2,
                  forgetCarrier final.2) :
                  ProbComp (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState))

/-! ## The predicate's own payoff

The projection law applies to the fused stage as soon as the handler forgets along the same map,
and that is the whole of what the widening costs. This is `ServingForget.run_fuseServing_map`
at `π` = take-the-cache, and the only reason it needs no extra hypothesis is that `Bracket` was
defined to be what it asks for. -/

/-- **The fused stage of a bracketed run forgets to an unbracketed one.** -/
theorem run_bracketed_map {α : Type}
    (handler : QueryImpl OracleWorld (StateT CountedState ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → CountedState → CountedState) (after : CountedState → CountedState)
    (hbefore : ∀ request : Message, Bracket (before request)) (hafter : Bracket after)
    (outer' : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (hforget : ServingForget.ForgetsAlong (fun state : CountedState => state.1.cache) handler
      outer')
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : ω) (log : SigningLog) (start : CountedState) :
    (fun step : α × (ω × SigningLog × CountedState) =>
        (step.1, (step.2.1, step.2.2.1, step.2.2.2.1.cache))) <$>
      (simulateQ (fuseServing handler inner before after) computation).run
        (accumulated, log, start) =
      (simulateQ (fuse outer' inner) computation).run (accumulated, log, start.1.cache) :=
  ServingForget.run_fuseServing_map (fun state : CountedState => state.1.cache) handler outer'
    inner before after (fun request state => (hbefore request state).1)
    (fun state => (hafter state).1) hforget computation accumulated log start

end SlhDsaSecurity.BracketedRun

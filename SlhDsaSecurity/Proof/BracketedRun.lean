import SlhDsaSecurity.Proof.ServingForget
import SlhDsaSecurity.Proof.LateProbes
import SlhDsaSecurity.Proof.RecorderView

/-!
# What a bracketed tail is, and why the predicate looks like this

`LateProbes.IsRecorderRun` asks a tail to **be** `simulateQ (recorder …) computation` for some
`computation : OracleComp OracleWorld _`. A carrier tail cannot be: the brackets write the
state between queries, and an `OracleComp OracleWorld` can only sample or query. So the
predicate has to widen, and this is the widening.

**The shape is not a choice, and that is the point.** A bracketed run is a fused phase whose
outer handler is a recorder, read through a projection that drops the writer, the log and
whatever the handler carries beside its cache. For the three consumers to survive, two things
have to be true of the brackets: they leave the cache alone, and they leave both recordings
alone. Those two are *exactly* the hypotheses of `ServingForget.run_fuseServing_map` —
`hbefore` and `hafter` at the projection that keeps the cache and the recordings.

So the predicate's side conditions and the lemma that discharges them are the same two facts,
written once. A predicate invented separately would have drifted from the lemma that feeds it,
which is a failure this development has paid for more than once; stating it this way is the
predicate being honest about what it needs rather than a convenience.

**What it does not fix.** The value — the outcome, the record and the count — is left to a
projection `value`, because where the count comes from is the tail's business and not the
predicate's. At the plain recorder it is `countAllHashes` inside the computation; a bracketed
game is not one computation, so a bracketed tail has to take its count from the handler's own
state instead. The predicate is agnostic about that, exactly as it is agnostic about what the
carrier carries, and for the same reason: nothing the three consumers do reads it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.BracketedRun

open Security RecorderView PhaseFusion

/-- The walk the tail is read at. -/
abbrev Walk : Type :=
  ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec

variable {σ : Type} [CacheView σ] {ω : Type} [Monoid ω]

/-- **The brackets touch neither the cache nor either recording.** The one condition a bracket
has to meet, and the one `ServingForget.run_fuseServing_map` asks for. -/
def Bracket (f : StateOf σ → StateOf σ) : Prop :=
  ∀ state : StateOf σ, CacheView.cacheOf (f state).1 = CacheView.cacheOf state.1 ∧
    (f state).2 = state.2

/-- The projection a bracketed run is read through: the cache, and the two recordings. -/
def forgetCarrier (state : StateOf σ) : SplitPrefix.SplitState :=
  (CacheView.cacheOf state.1, state.2)

theorem forgetCarrier_of_bracket {f : StateOf σ → StateOf σ} (hf : Bracket f)
    (state : StateOf σ) : forgetCarrier (f state) = forgetCarrier state := by
  rw [forgetCarrier, forgetCarrier, (hf state).1, (hf state).2]

/-- **A bracketed recorder run.** The tail is a fused phase over a recorder, with brackets that
move only what the projection drops, read through that projection. -/
def IsBracketedRecorderRun
    (leftKeep rightKeep : Walk → Bytes → σ → Prop)
    (fused : LateProbes.FusedTail) (adversary : Adversary) : Prop :=
  ∀ walk ∈ support WarmedGame.graphWalk,
    ∃ (α : Type) (computation : OracleComp (OracleWorld + SigningSpec) α)
      (inner : QueryImpl (OracleWorld + SigningSpec)
        (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
      (before : Message → StateOf σ → StateOf σ) (after : StateOf σ → StateOf σ)
      (accumulated : ω) (log : SigningLog) (start : StateOf σ)
      (value : α × (ω × SigningLog × StateOf σ) → (Outcome × Multiset Bytes) × Nat),
      forgetCarrier start = (walk.2, [], []) ∧
        (∀ request : Message, Bracket (before request)) ∧ Bracket after ∧
        fused adversary walk =
          (fun z => (value z, forgetCarrier z.2.2.2)) <$>
            (simulateQ (fuseServing (noticingRecorderOf (leftKeep walk) (rightKeep walk))
              inner before after) computation).run (accumulated, log, start)

/-! ## The predicate's own payoff

The projection law applies to a bracketed run as soon as the handler forgets along the same
map, and that is the whole of what the widening costs: a tail that is a bracketed recorder run
projects to the unbracketed fused run exactly, so anything stated at the latter moves to the
former. This is `ServingForget.run_fuseServing_map` at `π` = take-the-cache, and the only reason
it applies without an extra hypothesis is that `Bracket` was defined to be what it asks for. -/

/-- **A bracketed run forgets to an unbracketed one.** Stated at the cache, which is the
projection `LateProbes.ForgetsTo` reads a tail through. -/
theorem run_bracketed_map {α : Type}
    (leftKeep rightKeep : Bytes → σ → Prop)
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → StateOf σ → StateOf σ) (after : StateOf σ → StateOf σ)
    (hbefore : ∀ request : Message, Bracket (before request)) (hafter : Bracket after)
    (outer' : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (hforget : ServingForget.ForgetsAlong (fun state : StateOf σ => CacheView.cacheOf state.1)
      (noticingRecorderOf leftKeep rightKeep) outer')
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (accumulated : ω) (log : SigningLog) (start : StateOf σ) :
    (fun step : α × (ω × SigningLog × StateOf σ) =>
        (step.1, (step.2.1, step.2.2.1, CacheView.cacheOf step.2.2.2.1))) <$>
      (simulateQ (fuseServing (noticingRecorderOf leftKeep rightKeep) inner before after)
        computation).run (accumulated, log, start) =
      (simulateQ (fuse outer' inner) computation).run
        (accumulated, log, CacheView.cacheOf start.1) :=
  ServingForget.run_fuseServing_map (fun state : StateOf σ => CacheView.cacheOf state.1)
    (noticingRecorderOf leftKeep rightKeep) outer' inner before after
    (fun request state => (hbefore request state).1) (fun state => (hafter state).1) hforget
    computation accumulated log start

end SlhDsaSecurity.BracketedRun

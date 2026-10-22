import SlhDsaSecurity.Proof.BracketedRun

/-!
# What a bracketed run keeps true of its recordings

`ServedAgreement.Files` is the interface a bracketed run is read through for the **carrier** —
the cache, the framing and the served set — and it keeps `τ`, where the two recordings live,
opaque. That opacity is the property that let it transport through the counter, so it is not a
gap to be filled in place: the recordings want their own interface, in the same shape.

This is that shape, and it is smaller, because everything the recordings need is of one form:
**a property of the state that every step preserves is preserved by a run, and by a bracketed
phase if the brackets preserve it too.** `BracketedRun.Bracket` already says the brackets touch
neither the cache nor either recording, so for any invariant reading only those two the bracket
condition is discharged rather than assumed.

Nothing here knows what a recording is. `right_record_nodup` and `messageClass_of_record` become
instances by supplying one step fact each, which is the only place the recorder's own shape
enters.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordInvariant

open Security BracketedRun PhaseFusion

variable {ω : Type} [Monoid ω]

/-- **A property every step preserves is preserved by a run.** -/
theorem run_invariant {Inv : CountedState → Prop}
    (handler : QueryImpl OracleWorld (StateT CountedState ProbComp))
    (hstep : ∀ (queried : OracleWorld.Domain) (state : CountedState)
      (step : OracleWorld.Range queried × CountedState),
      step ∈ support ((handler queried).run state) → Inv state → Inv step.2)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : CountedState) (result : α × CountedState),
      result ∈ support ((simulateQ handler computation).run state) → Inv state →
        Inv result.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hinv
  | query_bind queried next ih =>
    intro state result hmem hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hs, hrest⟩ := hmem
    exact ih step.1 step.2 result hrest (hstep queried state step hs hinv)

/-- **And by a bracketed phase**, given that the brackets preserve it. -/
theorem phase_invariant {Inv : CountedState → Prop}
    (handler : QueryImpl OracleWorld (StateT CountedState ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → CountedState → CountedState) (after : CountedState → CountedState)
    (hstep : ∀ (queried : OracleWorld.Domain) (state : CountedState)
      (step : OracleWorld.Range queried × CountedState),
      step ∈ support ((handler queried).run state) → Inv state → Inv step.2)
    (hbefore : ∀ (request : Message) (state : CountedState), Inv state → Inv (before request state))
    (hafter : ∀ state : CountedState, Inv state → Inv (after state))
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (accumulated : ω) (log : SigningLog) (carrier : CountedState)
      (result : α × (ω × SigningLog × CountedState)),
      result ∈ support ((simulateQ (fuseServing handler inner before after) computation).run
        (accumulated, log, carrier)) → Inv carrier → Inv result.2.2.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [show result.2.2.2 = carrier from by rw [hmem]]
    exact hinv
  | query_bind queried next ih =>
    intro accumulated log carrier result hmem hinv
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hs, hrest⟩ := hmem
    refine ih step.1 step.2.1 step.2.2.1 step.2.2.2 result hrest ?_
    rcases queried with world | request
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inl world)).run).run log)).run carrier >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inl world) ×
                (ω × SigningLog × CountedState)))) := hs
      obtain ⟨z, hz, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact run_invariant handler hstep _ carrier z hz hinv
    · have hs' : step ∈ support
          ((simulateQ handler (((inner (Sum.inr request)).run).run log)).run
              (before request carrier) >>= fun z =>
            (pure (z.1.1.1, (accumulated * z.1.1.2, z.1.2, after z.2)) :
              ProbComp ((OracleWorld + SigningSpec).Range (Sum.inr request) ×
                (ω × SigningLog × CountedState)))) := hs
      obtain ⟨z, hz, hpure⟩ := support_bind_exists hs'
      rw [show step.2.2.2 = after z.2 from congrArg (fun p => p.2.2.2) hpure]
      exact hafter z.2
        (run_invariant handler hstep _ (before request carrier) z hz
          (hbefore request carrier hinv))

/-! ## The bracket condition, discharged rather than assumed

An invariant that reads only the cache and the two recordings is preserved by any `Bracket`,
because that is exactly what a bracket is defined to leave alone. -/

theorem bracket_invariant {Inv : CountedState → Prop}
    (hreads : ∀ left right : CountedState,
      left.1.cache = right.1.cache → left.2.1 = right.2.1 → Inv left → Inv right)
    {f : CountedState → CountedState} (hf : Bracket f) (state : CountedState)
    (hinv : Inv state) : Inv (f state) :=
  hreads state (f state) (hf state).1.symm (hf state).2.symm hinv

end SlhDsaSecurity.RecordInvariant

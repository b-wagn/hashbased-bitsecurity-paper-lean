import SlhDsaSecurity.Proof.OpenCache

/-!
# Which cell a probe is charged against, and the flag that records it

`OpenCache.evalDist_stalled_lazyProgram_congr` says the stalled run does not mention the cell
it stalled on. To use it the charge has to be expressed as an event about that run, and a
probe has to be charged against *one* cell rather than against the table as a whole. This file
does both.

**One cell per probe.** `SensitiveAt` names the cell a candidate is charged against, and
`sensitiveAt_unique` is the lemma that keeps the rate at one unit per probe:
`Stakes.locate` reads the node off the address before any cell is consulted, and `Stakes.stake`
reads the cell off the node, so a candidate is charged against at most one cell. The events
"this probe is charged against cell `i`" are therefore disjoint as `i` ranges over the cells,
and summing them counts each probe once. Stated loosely — a bound per cell, added over cells —
the same sum would come to `|Index| / 2 ^ 128` per probe, which is useless; that is why the
disjointness is a named lemma and not a step inside a calculation.

**The flag.** `StalledRun.probEvent_flag_stalled_eq` wants the event carried as a sticky flag in
the handler's state, so `flagged` is `OpenCache.lazyProgram` with one added: a flag set when a
probe is charged against the stalled cell. It reads that cell, which is exactly why it is a
different handler from the blind one and why the two are only ever joined through the record —
`flag_iff_record` is that joining, and it is the only place their relationship is used.

The three hypotheses the stalled comparison takes hold for concrete reasons: the handler never
fails, availability only grows along a run so a released cell stays released, and a charge
requires the cell to be unavailable, so none can arise once it is released.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.ChargedProbe

open CanonicalGraph SensitiveQuery OpenCache

variable {Node : Type}

/-! ## One cell per probe -/

/-- A candidate input is charged **against a given cell**: it is the canonical input of a node
staking that cell, and the signatures have not made it available. -/
def SensitiveAt (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) (index : CanonicalGraph.Node) : Prop :=
  ∃ node : Node, stakes.stake node = index ∧ unavailable cache index ∧
    stakes.inputOf node (cells index) = candidate

/-- Being charged at some cell is being charged. -/
theorem sensitive_iff_exists (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) :
    Sensitive stakes unavailable cells cache candidate ↔
      ∃ index, SensitiveAt stakes unavailable cells cache candidate index := by
  constructor
  · rintro ⟨node, hunavailable, hinput⟩
    exact ⟨stakes.stake node, node, rfl, hunavailable, hinput⟩
  · rintro ⟨index, node, hstake, hunavailable, hinput⟩
    exact ⟨node, hstake ▸ hunavailable, hstake ▸ hinput⟩

/-- **A probe is charged against at most one cell.** The address names the node before any cell
is read and the node names the cell, so the events "this probe is charged against cell `i`" are
disjoint as `i` ranges over the cells — which is what makes their sum one unit per probe rather
than one per cell. -/
theorem sensitiveAt_unique (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (cache : QueryCache HashSpec) (candidate : Bytes) {first second : CanonicalGraph.Node}
    (hfirst : SensitiveAt stakes unavailable cells cache candidate first)
    (hsecond : SensitiveAt stakes unavailable cells cache candidate second) :
    first = second := by
  obtain ⟨node, hstake, -, hinput⟩ := hfirst
  obtain ⟨other, hother, -, hotherInput⟩ := hsecond
  have hnodes : node = other := by
    have hleft : stakes.locate candidate = some node := by
      rw [← hinput, stakes.locate_inputOf]
    have hright : stakes.locate candidate = some other := by
      rw [← hotherInput, stakes.locate_inputOf]
    exact Option.some.inj (hleft.symm.trans hright)
  rw [← hstake, ← hother, hnodes]

/-! ## The flag -/

/-- The probe a query makes, if it makes one. -/
def probeOf : OracleWorld.Domain → Option Bytes
  | Sum.inl _ => none
  | Sum.inr input => some input

/-- A recorded entry charged against a given cell. -/
def Charged (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (entry : Bytes × QueryCache HashSpec) : Prop :=
  SensitiveAt stakes unavailable cells entry.2 entry.1 index

/-- A query charged against a given cell at a given state. -/
def ChargedHere (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop) (cells : Cells)
    (index : CanonicalGraph.Node) (state : HandlerState)
    (queried : OracleWorld.Domain) : Prop :=
  ∃ input, probeOf queried = some input ∧
    SensitiveAt stakes unavailable cells state.1 input index

variable (publicSeed : Digest)

open scoped Classical in
/-- **The flagged handler**: the one that answers only what a run may legitimately compute,
with a sticky flag set when a probe is charged against `index`. -/
noncomputable def flagged (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT (HandlerState × Bool) ProbComp) :=
  fun queried state => do
    let step ← ((lazyProgram publicSeed availableAt table) queried).run state.1
    pure (step.1, (step.2, state.2 ||
      decide (ChargedHere stakes (fun cache index => ¬ availableAt cache index) table.1 index
        state.1 queried)))

open scoped Classical in
theorem flagged_run (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    ((flagged publicSeed availableAt stakes index table) queried).run state =
      ((lazyProgram publicSeed availableAt table) queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2 ||
          decide (ChargedHere stakes (fun cache index => ¬ availableAt cache index) table.1
            index state.1 queried))) : ProbComp _) := rfl


open scoped Classical in
/-- A private sample leaves the handler's state alone. -/
theorem lazyProgram_step_inl (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (coin : unifSpec.Domain) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inl coin) × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table)
      (Sum.inl coin)).run state)) : step.2 = state := by
  rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
  obtain ⟨value, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  exact congrArg Prod.snd hpure

open scoped Classical in
/-- A hash query records itself with the cache it was issued against. -/
theorem lazyProgram_step_inr (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (input : Bytes) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inr input) × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table)
      (Sum.inr input)).run state)) : step.2.2.1 = state.2.1 ++ [(input, state.1)] := by
  rw [lazyProgram_run_inr, mem_support_bind_iff] at hstep
  obtain ⟨inner, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-! ## What the stalled comparison takes

Three facts, each for a concrete reason: the handler never fails, availability only grows along
a run so a released cell stays released, and a charge requires the cell to be unavailable, so
none can arise once it is released. -/

open scoped Classical in
/-- The handler never fails. -/
theorem lazyProgram_neverFails (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState) :
    Pr[⊥ | ((lazyProgram publicSeed availableAt table) queried).run state] = 0 := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl]
    simp
  · rw [lazyProgram_run_inr]
    cases hcached : state.1 input with
    | some cached => simp
    | none =>
      cases hopen : openCache publicSeed (availableAt state.1) table input with
      | some answer => simp
      | none => simp

open scoped Classical in
/-- Cache entries survive a step, so what a run has determined only grows. -/
theorem lazyProgram_cache_mono (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed availableAt table) queried).run state))
    (probe : Bytes) (hprobe : state.1 probe ≠ none) : step.2.1 probe ≠ none := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hprobe
  · rw [lazyProgram_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨inner, hinner, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    show inner.2 probe ≠ none
    have hgrow : inner.2 = state.1 ∨
        ∃ answer : HashOutput, inner.2 = state.1.cacheQuery input answer := by
      revert hinner
      cases hcached : state.1 input with
      | some cached =>
        intro hinner
        simp only [support_pure, Set.mem_singleton_iff] at hinner
        exact Or.inl (congrArg Prod.snd hinner)
      | none =>
        cases hopen : openCache publicSeed (availableAt state.1) table input with
        | some answer =>
          intro hinner
          simp only [support_pure, Set.mem_singleton_iff] at hinner
          exact Or.inr ⟨answer, congrArg Prod.snd hinner⟩
        | none =>
          intro hinner
          simp only [support_map] at hinner
          obtain ⟨sampled, -, hpair⟩ := hinner
          exact Or.inr ⟨sampled, (congrArg Prod.snd hpair).symm⟩
    rcases hgrow with hsame | ⟨answer, hcache⟩
    · rw [hsame]; exact hprobe
    · rw [hcache]
      by_cases hsame : probe = input
      · subst hsame
        rw [QueryCache.cacheQuery_self]
        simp
      · rw [QueryCache.cacheQuery_of_ne state.1 answer hsame]
        exact hprobe

open scoped Classical in
/-- The flagged handler never fails either. -/
theorem flagged_neverFails (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    Pr[⊥ | ((flagged publicSeed availableAt stakes index table) queried).run state] = 0 := by
  rw [flagged_run, probFailure_bind_eq_add_tsum,
    lazyProgram_neverFails publicSeed availableAt table queried state.1]
  simp

open scoped Classical in
/-- **A released cell stays released.** Availability grows with the cache, and the cache only
grows, so a state where the cell is available is followed by states where it is. -/
theorem flagged_frozen (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
        ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((flagged publicSeed availableAt stakes index table) queried).run
      state)) : availableAt step.2.1.1 index := by
  classical
  rw [flagged_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact hmono state.1.1 inner.2.1
    (fun probe hprobe =>
      lazyProgram_cache_mono publicSeed availableAt table queried state.1 inner hinner probe
        hprobe)
    index hstate

open scoped Classical in
/-- **No charge arises once the cell is released.** A charge needs the cell to be unavailable,
so a state where it is available is followed by states with the same flag. -/
theorem flagged_quiet (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((flagged publicSeed availableAt stakes index table) queried).run
      state)) : step.2.2 = state.2 := by
  classical
  rw [flagged_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, -, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show (state.2 || decide (ChargedHere stakes (fun cache node => ¬ availableAt cache node)
    table.1 index state.1 queried)) = state.2
  have hnone : ¬ ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1 index
      state.1 queried := by
    rintro ⟨probe, -, -, -, hunavailable, -⟩
    exact hunavailable hstate
  rw [decide_eq_false hnone, Bool.or_false]

/-! ## The flag is the record

The only place the flagged handler and the blind one are related: they record the same probes,
and the flag says exactly that one of them was charged. -/

open scoped Classical in
/-- **The flag says that a recorded probe was charged.** -/
theorem flag_iff_record {α : Type}
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (computation : OracleComp OracleWorld α)
    (state : HandlerState × Bool)
    (hstate : state.2 = true ↔ ∃ entry ∈ state.1.2.1,
      Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry)
    (result : α × (HandlerState × Bool))
    (hresult : result ∈ support ((simulateQ
      (flagged publicSeed availableAt stakes index table) computation).run state)) :
    result.2.2 = true ↔ ∃ entry ∈ result.2.1.2.1,
      Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]
    exact hstate
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hrest⟩ := hresult
    refine ih step.1 step.2 ?_ result hrest
    rw [flagged_run, mem_support_bind_iff] at hstep
    obtain ⟨inner, hinner, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rcases queried with coin | probe
    · have hsame : inner.2 = state.1 :=
        lazyProgram_step_inl publicSeed availableAt table coin state.1 inner hinner
      have hnone : ¬ ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1
          index state.1 (Sum.inl coin) := by
        rintro ⟨candidate, hcandidate, -⟩
        simp [probeOf] at hcandidate
      rw [hpure]
      show (state.2 || decide (ChargedHere stakes
          (fun cache node => ¬ availableAt cache node) table.1 index state.1 (Sum.inl coin)))
            = true ↔
        ∃ entry ∈ inner.2.2.1,
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry
      rw [decide_eq_false hnone, Bool.or_false, hsame]
      exact hstate
    · have hrec : inner.2.2.1 = state.1.2.1 ++ [(probe, state.1.1)] :=
        lazyProgram_step_inr publicSeed availableAt table probe state.1 inner hinner
      have hhere : ChargedHere stakes (fun cache node => ¬ availableAt cache node) table.1 index
          state.1 (Sum.inr probe) ↔
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index
            (probe, state.1.1) := by
        constructor
        · rintro ⟨candidate, hcandidate, hsensitive⟩
          have hsame : candidate = probe := by
            have := hcandidate
            simp [probeOf] at this
            exact this.symm
          rw [hsame] at hsensitive
          exact hsensitive
        · intro hcharged
          exact ⟨probe, rfl, hcharged⟩
      rw [hpure]
      show (state.2 || decide (ChargedHere stakes
          (fun cache node => ¬ availableAt cache node) table.1 index state.1 (Sum.inr probe)))
            = true ↔
        ∃ entry ∈ inner.2.2.1,
          Charged stakes (fun cache node => ¬ availableAt cache node) table.1 index entry
      rw [hrec, Bool.or_eq_true, decide_eq_true_eq, hhere, hstate]
      simp [or_comm]

end SlhDsaSecurity.ChargedProbe

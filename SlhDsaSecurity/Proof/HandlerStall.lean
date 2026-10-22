import SlhDsaSecurity.Proof.HandlerFacts

/-!
# The stall, at any handler that satisfies the four facts

`ChargedProbe`'s stalled layer — the handler never fails, a released cell stays released, the
weight and the charge stand still once it is released, and the stalled run is blind to it — is
written at `OpenCache.lazyProgram`. `HandlerFacts.Facts` says which four properties of that
handler those proofs use. This file is the same layer with the handler abstract and `Facts` in
its place, so that `ServingProgram.servingProgram` gets it too.

Nothing here is new mathematics; what is new is **where each hypothesis is discharged**. The
originals reach for `lazyProgram_neverFails`, `CacheAvailability.lazyProgram_persists`,
`lazyProgram_step_inl`/`_inr` and `lazyProgram_step_congr`; the copies reach for `neverFails`,
`grows`, `record` and `blind`. That is the whole difference, and it is why the copies are
shorter than the originals rather than longer.

`StalledRun` itself needed nothing: it was already stated at an arbitrary handler, so the stall
is reached here by instantiating it rather than by repeating it.

**The copy is deliberately a copy.** `ChargedProbe`'s and `RedrawCell`'s existing statements
stay exactly as they are, as instances to retire once their readers can move; a parameterisation
landing as a replacement would make a merge hazard of every file that reads the charge, for as
long as that takes.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000

namespace SlhDsaSecurity.HandlerStall

open CanonicalGraph SensitiveQuery OpenCache ChargedProbe HandlerFacts

variable {Node : Type}

variable (publicSeed : Digest)

/-! ## What a step does to the record

Two readings of `Facts.record`, one per kind of query: a coin leaves the record alone and a
hash call appends its own probe with the carrier it was issued against. -/

/-- A private sample leaves the record alone. -/
theorem record_inl
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl) (table : Cells × Padding)
    (coin : unifSpec.Domain) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inl coin) × HandlerState)
    (hstep : step ∈ support (((impl table) (Sum.inl coin)).run state)) :
    step.2.2.1 = state.2.1 := by
  rw [hfacts.record table (Sum.inl coin) state step hstep]
  exact List.append_nil _

/-- A hash query records itself with the carrier it was issued against. -/
theorem record_inr
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl) (table : Cells × Padding)
    (input : Bytes) (state : HandlerState)
    (step : OracleWorld.Range (Sum.inr input) × HandlerState)
    (hstep : step ∈ support (((impl table) (Sum.inr input)).run state)) :
    step.2.2.1 = state.2.1 ++ [(input, state.1)] :=
  hfacts.record table (Sum.inr input) state step hstep

/-! ## The flag carried untouched -/

/-- Carrying a flag it does not touch leaves the handler failure-free. -/
theorem withFlag_neverFails
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    Pr[⊥ | ((withFlag (impl table)) queried).run state] = 0 := by
  rw [withFlag_run, probFailure_bind_eq_add_tsum, hfacts.neverFails table queried state.1]
  simp

/-- A released cell stays released, the flag being untouched. -/
theorem withFlag_frozen
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (index : CanonicalGraph.Node) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt table state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (impl table)) queried).run state)) :
    availableAt table step.2.1.1 index := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact hmono table state.1.1 inner.2.1 (hfacts.grows table queried state.1 inner hinner)
    index hstate

open scoped Classical in
/-- **Once the cell is released nothing more aims at it**, counting distinct probes. -/
theorem withFlag_aiming_dedup_quiet
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt table state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (impl table)) queried).run state)) :
    aiming stakes (fun cache node => ¬ availableAt table cache node) index step.2.1.2.1.dedup =
      aiming stakes (fun cache node => ¬ availableAt table cache node) index
        state.1.2.1.dedup := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show aiming stakes (fun cache node => ¬ availableAt table cache node) index inner.2.2.1.dedup = _
  rcases queried with coin | probe
  · rw [record_inl publicSeed availableAt impl hfacts table coin state.1 inner hinner]
  · rw [record_inr publicSeed availableAt impl hfacts table probe state.1 inner hinner]
    have hnot : ¬ Targets stakes (fun cache node => ¬ availableAt table cache node) index
        (probe, state.1.1) := by
      rintro ⟨-, -, hunavailable, -⟩
      exact hunavailable hstate
    rw [aiming_dedup_eq_card, aiming_dedup_eq_card,
      show (state.1.2.1 ++ [(probe, state.1.1)]).toFinset =
        insert (probe, state.1.1) state.1.2.1.toFinset from by simp,
      Finset.filter_insert, if_neg hnot]

open scoped Classical in
/-- Once the cell is released nothing more is charged against it. -/
theorem withFlag_charged_quiet
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (queried : OracleWorld.Domain) (state : HandlerState × Bool)
    (hstate : availableAt table state.1.1 index)
    (step : OracleWorld.Range queried × (HandlerState × Bool))
    (hstep : step ∈ support (((withFlag (impl table)) queried).run state)) :
    ((∃ entry ∈ step.2.1.2.1, ChargedBy stakes
        (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry) ↔
      ∃ entry ∈ state.1.2.1, ChargedBy stakes
        (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry) := by
  classical
  rw [withFlag_run, mem_support_bind_iff] at hstep
  obtain ⟨inner, hinner, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show (∃ entry ∈ inner.2.2.1, _) ↔ _
  rcases queried with coin | probe
  · rw [record_inl publicSeed availableAt impl hfacts table coin state.1 inner hinner]
  · rw [record_inr publicSeed availableAt impl hfacts table probe state.1 inner hinner]
    have hnot : ¬ ChargedBy stakes (fun cache node => ¬ availableAt table cache node) index
        (table.1 index) (probe, state.1.1) := by
      rintro ⟨-, -, hunavailable, -⟩
      exact hunavailable hstate
    constructor
    · rintro ⟨entry, hentry, hcharged⟩
      rcases List.mem_append.mp hentry with hleft | hright
      · exact ⟨entry, hleft, hcharged⟩
      · rw [List.mem_singleton.mp hright] at hcharged
        exact absurd hcharged hnot
    · rintro ⟨entry, hentry, hcharged⟩
      exact ⟨entry, List.mem_append.mpr (Or.inl hentry), hcharged⟩

/-! ## The stall changes nothing the charge reads -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The expected number of distinct probes aiming at a cell is the same stalled and
unstalled.** -/
theorem expected_aiming_stalled_eq {α : Type}
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    (∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (withFlag (impl table)) computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
            z.2.1.2.1.dedup : Nat) : ℝ≥0∞)) =
      ∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (StalledRun.stalled (withFlag (impl table))
            (fun inner => availableAt table inner.1 index) stall) computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
            z.2.1.2.1.dedup : Nat) : ℝ≥0∞) :=
  StalledRun.expectation_stalled_eq (withFlag (impl table))
    (fun inner => availableAt table inner.1 index) stall
    (fun p => ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
      p.1.2.1.dedup : Nat) : ℝ≥0∞))
    (fun queried p => withFlag_neverFails publicSeed availableAt impl hfacts table queried p)
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt impl hfacts hmono index table queried p hp z hz)
    (fun queried p hp z hz => by
      exact_mod_cast congrArg (fun count : Nat => (count : ℝ≥0∞))
        (withFlag_aiming_dedup_quiet publicSeed availableAt impl hfacts stakes index table
          queried p hp z hz))
    computation state

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Stalling does not change the chance of a charged probe.** -/
theorem prob_charged_stalled_eq {α : Type}
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    Pr[fun z : α × (HandlerState × Bool) =>
        ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
          (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry |
      (simulateQ (withFlag (impl table)) computation).run state] =
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry |
        (simulateQ (StalledRun.stalled (withFlag (impl table))
          (fun inner => availableAt table inner.1 index) stall) computation).run state] := by
  classical
  have hform : ∀ run : ProbComp (α × (HandlerState × Bool)),
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry | run] =
        ∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          (if ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry
            then 1 else 0) := by
    intro run
    rw [probEvent_eq_tsum_ite]
    refine tsum_congr fun z => ?_
    by_cases hz : ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
        (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry
    · simp [hz]
    · simp [hz]
  rw [hform, hform]
  exact StalledRun.expectation_stalled_eq (withFlag (impl table))
    (fun inner => availableAt table inner.1 index) stall
    (fun p => if ∃ entry ∈ p.1.2.1, ChargedBy stakes
      (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry then 1 else 0)
    (fun queried p => withFlag_neverFails publicSeed availableAt impl hfacts table queried p)
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt impl hfacts hmono index table queried p hp z hz)
    (fun queried p hp z hz => if_congr
      (withFlag_charged_quiet publicSeed availableAt impl hfacts stakes index table queried p hp
        z hz) rfl rfl) computation state

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **Stalling does not change the chance that a claim is charged.** The claims are read at the
run's own final carrier, so once the stall has fired none of them is charged at all. -/
theorem prob_claimed_stalled_eq {α : Type}
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool)
    (claims : α × (HandlerState × Bool) → List (Bytes × HandlerCarrier.State))
    (hcache : ∀ (z : α × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State),
      entry ∈ claims z → entry.2 = z.2.1.1) :
    Pr[fun z : α × (HandlerState × Bool) =>
        ∃ entry ∈ claims z, ChargedBy stakes
          (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry |
      (simulateQ (withFlag (impl table)) computation).run state] =
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ claims z, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry |
        (simulateQ (StalledRun.stalled (withFlag (impl table))
          (fun inner => availableAt table inner.1 index) stall) computation).run state] := by
  classical
  have hform : ∀ run : ProbComp (α × (HandlerState × Bool)),
      Pr[fun z : α × (HandlerState × Bool) =>
          ∃ entry ∈ claims z, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry | run] =
        ∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          (if ∃ entry ∈ claims z, ChargedBy stakes
            (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry
            then 1 else 0) := by
    intro run
    rw [probEvent_eq_tsum_ite]
    refine tsum_congr fun z => ?_
    by_cases hz : ∃ entry ∈ claims z, ChargedBy stakes
        (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry
    · simp [hz]
    · simp [hz]
  rw [hform, hform]
  refine StalledRun.expectation_stalled_eq_of_zero (withFlag (impl table))
    (fun inner => availableAt table inner.1 index) stall
    (fun z => if ∃ entry ∈ claims z, ChargedBy stakes
      (fun cache node => ¬ availableAt table cache node) index (table.1 index) entry then 1 else 0)
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt impl hfacts hmono index table queried p hp z hz)
    (fun z hz => if_neg ?_) computation state
  rintro ⟨entry, hentry, -, -, hunavailable, -⟩
  exact hunavailable (by rw [hcache z entry hentry]; exact hz)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The expected number of distinct claims aiming at a cell is the same stalled and
unstalled.** -/
theorem expected_aiming_claimed_stalled_eq {α : Type}
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Node CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (table : Cells × Padding) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool)
    (claims : α × (HandlerState × Bool) → List (Bytes × HandlerCarrier.State))
    (hcache : ∀ (z : α × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State),
      entry ∈ claims z → entry.2 = z.2.1.1) :
    (∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (withFlag (impl table)) computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
            (claims z).dedup : Nat) : ℝ≥0∞)) =
      ∑' z : α × (HandlerState × Bool),
        Pr[= z | (simulateQ (StalledRun.stalled (withFlag (impl table))
            (fun inner => availableAt table inner.1 index) stall) computation).run state] *
          ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
            (claims z).dedup : Nat) : ℝ≥0∞) := by
  classical
  refine StalledRun.expectation_stalled_eq_of_zero (withFlag (impl table))
    (fun inner => availableAt table inner.1 index) stall
    (fun z => ((aiming stakes (fun cache node => ¬ availableAt table cache node) index
      (claims z).dedup : Nat) : ℝ≥0∞))
    (fun queried p hp z hz =>
      withFlag_frozen publicSeed availableAt impl hfacts hmono index table queried p hp z hz)
    (fun z hz => ?_) computation state
  have hnil : (claims z).dedup.filter (fun entry => decide (Targets stakes
      (fun cache node => ¬ availableAt table cache node) index entry)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro entry hentry hdecide
    obtain ⟨-, -, hunavailable, -⟩ := of_decide_eq_true hdecide
    exact hunavailable (by rw [hcache z entry (List.mem_dedup.mp hentry)]; exact hz)
  rw [aiming, hnil]
  simp

/-! ## The stalled run is blind to the cell it stalled on -/

/-- **The stalled run does not mention the cell it stalled on.**

The two sides stall against the availability of **their own** table, and the first thing the
proof does is to make those one predicate — which is what `availBlind` is for. Without it the
comparison would be between runs stalling at different moments, and `StalledRun`'s own
congruence, which takes a single `Frozen`, would not even apply.

The relation the congruence is run at carries that identification along: `AgreeOff index` alone
would leave the per-step hypothesis quantified over tables unrelated to this pair, and the
unfrozen condition could not be transported to them. -/
theorem evalDist_stalled_congr {α : Type}
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (index : CanonicalGraph.Node) (hallowed : allowed index)
    (left right : Cells × Padding) (hagree : AgreeOff index left right)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (oa : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    𝒟[(simulateQ (StalledRun.stalled (withFlag (impl left))
          (fun inner => availableAt left inner.1 index) stall) oa).run state] =
      𝒟[(simulateQ (StalledRun.stalled (withFlag (impl right))
          (fun inner => availableAt right inner.1 index) stall) oa).run state] := by
  rw [show availableAt right = availableAt left from
    (hfacts.availBlind index hallowed left right hagree).symm]
  exact StalledRun.evalDist_stalled_congr (fun table => withFlag (impl table))
    (fun inner => availableAt left inner.1 index) stall
    (fun first second => AgreeOff index first second ∧ availableAt first = availableAt left)
    (fun queried p first second hfirst hfrozen => by
      rw [withFlag_run, withFlag_run,
        hfacts.blind index hallowed first second hfirst.1 queried p.1
          (by rw [hfirst.2]; exact hfrozen)])
    oa left right ⟨hagree, rfl⟩ state

end SlhDsaSecurity.HandlerStall

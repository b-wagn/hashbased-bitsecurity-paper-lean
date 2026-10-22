import SlhDsaSecurity.Proof.HandlerStall
import SlhDsaSecurity.Proof.RedrawCell

/-!
# The charge, at any handler that satisfies the four facts

`HandlerStall` is `ChargedProbe`'s stalled layer with the handler abstract. This file is the
layer above it — `RedrawCell`'s stall-redraw-weigh argument and the sum over cells that turns it
into a charge against a whole run — with the handler abstract in the same way.

The three steps are unchanged. Stalling at a cell leaves the chance of a charge against it
alone; the stalled run does not read that cell, so it may be drawn after; and the drawn cell
costs the probes aiming at it, which stalling also leaves alone. What changes is that the second
step is `Facts.blind` rather than `OpenCache.lazyProgram_step_congr`, and so **`hclosed`
disappears from every statement here**: closure of availability under the structure was only
ever used to prove that one congruence, and a handler that satisfies `Facts` has already paid
for it. That is the clearest measure of what the interface is worth — a hypothesis that four
theorems carried is now carried by the handler's own construction, once.

**What appears in its place is `hcover : ∀ node, ¬ touched node → allowed node`**, and it is
where the real demand lives. `Facts.blind` is guarded, because a handler may read the table in
ways that make it false at particular cells — the one the chain ends at reads the public key,
whose root *is* a cell. Every use of `blind` here is at an index already shown untouched, so
`hcover` is exactly the promise that the handler is blind wherever this charge looks, and
nothing more is asked of it.

What is not here is the top of `RedrawCell`'s stack, `prob_game_sensitive_le`, because its
remaining step is of a different kind: it compares the handler at the real availability with the
handler at total availability, through `ChargedProbe.sensitiveFlagged`, and that comparison is
built from `openCache` rather than read off the four facts. It needs its own parameterisation,
at the handler's own lenient twin.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.HandlerCharge

open CanonicalGraph SensitiveQuery OpenCache ChargedProbe HandlerFacts

variable {Target : Type}

/-! ## The value a run returns is one the computation could produce

The charge's event is read **outside** the table draw, on the pair the redraw hands back, so
the availability it reads must be a function of the run's value. What connects that value to
the table is this: whatever a simulated run returns, the computation at that table could have
returned it. So a hypothesis stated about the computation's own values reaches every run of it,
stalled or not, and that is the only bridge the pass needs. -/

/-- **A simulated run's value is one the computation could have produced.** -/
theorem value_mem_support {β σ : Type}
    (handler : QueryImpl OracleWorld (StateT σ ProbComp)) (oa : OracleComp OracleWorld β)
    (start : σ) (z : β × σ) (hz : z ∈ support ((simulateQ handler oa).run start)) :
    z.1 ∈ support oa := by
  refine support_simulateQ_run'_subset handler oa start ?_
  show z.1 ∈ support (Prod.fst <$> (simulateQ handler oa).run start)
  rw [support_map]
  exact ⟨z, hz, rfl⟩

/-! ## What is charged, and what is admitted

`hreads` no longer says `unavailableOf` **is** `¬ availableAt`; it says it is
`¬ availableAt ∧ admitAt`, for a condition `admitAt` on the carrier alone.

**Narrowing it narrows the event and the weight by exactly the same amount, and for free.**
`ChargedProbe.Targets` and `ChargedProbe.SensitiveAt` both read `unavailable entry.2 index`, so
the probes that leave the count are the probes that leave the event. There is no soundness
argument to make beyond those two definitions, which is the reason to narrow here rather than by
a filter on the sum.

What it is for is the honest phase. Its probes are charged under `¬ availableAt` —
`GraphStakes.not_available_wotsHashNode_child` says why, and `WotsEntry.queriesUnder_chain` says
they are really made — and they are not in the record the half pays from, so the weight has to
lose them. The condition that tells them apart is one the handler can see: a probe made while a
signing frame is in flight is the signer's. `ServedAgreement.startServingOn` raises that frame
and `HandlerCarrier.State.framing` carries it, so `fun cache => cache.framing = none` is the
instance to come. Every caller today passes `fun _ => True`, which is the old statement.

**The handler's own `availableAt` is untouched, and must be.** `HandlerStall.withFlag_frozen`
needs it monotone along the run, and a frame raised and lowered again is not.
-/

/-! ## The charge against one cell -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The charge against one cell.** The weight is the number of **distinct** probes aiming at
it: a repeated probe is one chance at the cell, and the containment that pays for this weight
speaks of the entry a probe installed, which a repeat does not install twice. -/
theorem prob_charged_index_le {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (touched : CanonicalGraph.Node → Prop) (hindex : ¬ touched index)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
        ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes (unavailableOf pair.1.1) index pair.2 entry |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells index))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
          ((aiming stakes (unavailableOf z.1) index z.2.1.2.1.dedup : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hstall : Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
      ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes (unavailableOf pair.1.1) index pair.2 entry |
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      let result ← (simulateQ (withFlag (impl (cells, pad)))
        (computation (cells, pad))).run state
      pure (result, cells index))] =
      Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
          ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes (unavailableOf pair.1.1) index pair.2
            entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
            (fun inner => availableAt (cells, pad) inner.1 index) stall)
            (computation (cells, pad))).run state
          pure (result, cells index))] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun cells => congrArg _ ?_
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun pad => congrArg _ ?_
    rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
    refine Eq.trans (probEvent_congr' (q := fun z : α × (HandlerState × Bool) =>
        ∃ entry ∈ z.2.1.2.1, ChargedBy stakes
          (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache) index
          (cells index) entry)
      (fun z hz => by
        simp only [Function.comp_apply]
        rw [hreads (cells, pad) z.1 (value_mem_support _ _ _ z hz)]) rfl)
      (Eq.trans ?_ (probEvent_congr' (q := fun z : α × (HandlerState × Bool) =>
        ((fun pair : (α × (HandlerState × Bool)) × Cell =>
          ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes (unavailableOf pair.1.1) index pair.2
            entry) ∘ fun result => (result, cells index)) z)
      (fun z hz => by
        simp only [Function.comp_apply]
        rw [hreads (cells, pad) z.1 (value_mem_support _ _ _ z hz)]) rfl))
    exact HandlerStall.prob_charged_stalled_eq publicSeed availableAt impl hfacts hmono stakes
      index (cells, pad)
      (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache)
      (fun _ _ h => h.1) stall
      (computation (cells, pad)) state
  have hredraw : 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
    refine RedrawCell.evalDist_redraw_coordinate index ($ᵗ Padding : ProbComp Padding) _ ?_
    intro cells other pad hagree
    rw [htouched (other, pad) (cells, pad) fun node hnode =>
      (hagree node fun heq => hindex (heq ▸ hnode)).symm]
    exact HandlerStall.evalDist_stalled_congr publicSeed availableAt impl hfacts index
      (hcover index hindex) (cells, pad) (other, pad) ⟨hagree, fun parent _ => rfl⟩ stall
      (computation (cells, pad)) state
  rw [hstall, probEvent_congr' (fun _ _ => Iff.rfl) hredraw]
  have hassoc : (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) =
      (do
        let result ← (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
            (fun inner => availableAt (cells, pad) inner.1 index) stall)
            (computation (cells, pad))).run state)
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) := by
    simp only [bind_assoc]
  rw [hassoc]
  refine le_trans (le_of_eq (probEvent_congr' (fun pair _ =>
    show (∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
        (unavailableOf pair.1.1) index pair.2 entry) ↔
      ∃ entry ∈ pair.1.2.1.2.1.dedup, ChargedBy stakes
        (unavailableOf pair.1.1) index pair.2 entry from
    ⟨fun ⟨entry, hentry, hcharged⟩ => ⟨entry, List.mem_dedup.mpr hentry, hcharged⟩,
      fun ⟨entry, hentry, hcharged⟩ =>
        ⟨entry, List.mem_dedup.mp hentry, hcharged⟩⟩) rfl)) ?_
  have hcell := prob_run_cell_le_indexed stakes
    (fun z : α × (HandlerState × Bool) => unavailableOf z.1) index
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
        (fun inner => availableAt (cells, pad) inner.1 index) stall)
        (computation (cells, pad))).run state)
    (fun z => z.2.1.2.1.dedup)
  refine le_trans hcell ?_
  refine ENNReal.div_le_div_right (le_of_eq ?_) _
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun pad => congrArg _ ?_
  have hconv : ∀ run : ProbComp (α × (HandlerState × Bool)),
      (∀ z ∈ support run, z.1 ∈ support (computation (cells, pad))) →
      (∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          ((aiming stakes (unavailableOf z.1) index z.2.1.2.1.dedup : Nat) : ℝ≥0∞)) =
        ∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          ((aiming stakes
            (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache) index
            z.2.1.2.1.dedup : Nat) : ℝ≥0∞) := by
    intro run hrun
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support run
    · rw [hreads (cells, pad) z.1 (hrun z hz)]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  rw [hconv _ fun z hz => value_mem_support _ _ _ z hz,
    hconv _ fun z hz => value_mem_support _ _ _ z hz]
  exact (HandlerStall.expected_aiming_stalled_eq publicSeed availableAt impl hfacts hmono
    stakes index (cells, pad)
      (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache)
      (fun _ _ h => h.1) stall
      (computation (cells, pad)) state).symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The charge against one cell, for the claims the run returns.** The same three steps, with
the stall carried by the claims' own vanishing: a claim is read at the carrier the run ends
with, so it aims nowhere once that carrier has the cell. -/
theorem prob_claimed_index_le {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (touched : CanonicalGraph.Node → Prop) (hindex : ¬ touched index)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool)
    (claims : α × (HandlerState × Bool) → List (Bytes × HandlerCarrier.State))
    (hcache : ∀ (z : α × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State),
      entry ∈ claims z → entry.2 = z.2.1.1) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
        ∃ entry ∈ claims pair.1, ChargedBy stakes
          (unavailableOf pair.1.1) index pair.2 entry |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells index))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
          ((aiming stakes (unavailableOf z.1) index (claims z).dedup : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hstall : Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
      ∃ entry ∈ claims pair.1, ChargedBy stakes
        (unavailableOf pair.1.1) index pair.2 entry |
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      let result ← (simulateQ (withFlag (impl (cells, pad)))
        (computation (cells, pad))).run state
      pure (result, cells index))] =
      Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
          ∃ entry ∈ claims pair.1, ChargedBy stakes
            (unavailableOf pair.1.1) index pair.2 entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
            (fun inner => availableAt (cells, pad) inner.1 index) stall)
            (computation (cells, pad))).run state
          pure (result, cells index))] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun cells => congrArg _ ?_
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun pad => congrArg _ ?_
    rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
    refine Eq.trans (probEvent_congr' (q := fun z : α × (HandlerState × Bool) =>
        ∃ entry ∈ claims z, ChargedBy stakes
          (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache) index
          (cells index) entry)
      (fun z hz => by
        simp only [Function.comp_apply]
        rw [hreads (cells, pad) z.1 (value_mem_support _ _ _ z hz)]) rfl)
      (Eq.trans ?_ (probEvent_congr' (q := fun z : α × (HandlerState × Bool) =>
        ((fun pair : (α × (HandlerState × Bool)) × Cell =>
          ∃ entry ∈ claims pair.1, ChargedBy stakes (unavailableOf pair.1.1) index pair.2
            entry) ∘ fun result => (result, cells index)) z)
      (fun z hz => by
        simp only [Function.comp_apply]
        rw [hreads (cells, pad) z.1 (value_mem_support _ _ _ z hz)]) rfl))
    exact HandlerStall.prob_claimed_stalled_eq publicSeed availableAt impl hfacts hmono stakes
      index (cells, pad)
      (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache)
      (fun _ _ h => h.1) stall
      (computation (cells, pad)) state claims hcache
  have hredraw : 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
    refine RedrawCell.evalDist_redraw_coordinate index ($ᵗ Padding : ProbComp Padding) _ ?_
    intro cells other pad hagree
    rw [htouched (other, pad) (cells, pad) fun node hnode =>
      (hagree node fun heq => hindex (heq ▸ hnode)).symm]
    exact HandlerStall.evalDist_stalled_congr publicSeed availableAt impl hfacts index
      (hcover index hindex) (cells, pad) (other, pad) ⟨hagree, fun parent _ => rfl⟩ stall
      (computation (cells, pad)) state
  rw [hstall, probEvent_congr' (fun _ _ => Iff.rfl) hredraw]
  have hassoc : (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
          (fun inner => availableAt (cells, pad) inner.1 index) stall)
          (computation (cells, pad))).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) =
      (do
        let result ← (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
            (fun inner => availableAt (cells, pad) inner.1 index) stall)
            (computation (cells, pad))).run state)
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) := by
    simp only [bind_assoc]
  rw [hassoc]
  refine le_trans (le_of_eq (probEvent_congr' (fun pair _ =>
    show (∃ entry ∈ claims pair.1, ChargedBy stakes
        (unavailableOf pair.1.1) index pair.2 entry) ↔
      ∃ entry ∈ (claims pair.1).dedup, ChargedBy stakes
        (unavailableOf pair.1.1) index pair.2 entry from
    ⟨fun ⟨entry, hentry, hcharged⟩ => ⟨entry, List.mem_dedup.mpr hentry, hcharged⟩,
      fun ⟨entry, hentry, hcharged⟩ =>
        ⟨entry, List.mem_dedup.mp hentry, hcharged⟩⟩) rfl)) ?_
  have hcell := prob_run_cell_le_indexed stakes
    (fun z : α × (HandlerState × Bool) => unavailableOf z.1) index
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (StalledRun.stalled (withFlag (impl (cells, pad)))
        (fun inner => availableAt (cells, pad) inner.1 index) stall)
        (computation (cells, pad))).run state)
    (fun z => (claims z).dedup)
  refine le_trans hcell ?_
  refine ENNReal.div_le_div_right (le_of_eq ?_) _
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun pad => congrArg _ ?_
  have hconv : ∀ run : ProbComp (α × (HandlerState × Bool)),
      (∀ z ∈ support run, z.1 ∈ support (computation (cells, pad))) →
      (∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          ((aiming stakes (unavailableOf z.1) index (claims z).dedup : Nat) : ℝ≥0∞)) =
        ∑' z : α × (HandlerState × Bool), Pr[= z | run] *
          ((aiming stakes
            (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache) index
            (claims z).dedup : Nat) : ℝ≥0∞) := by
    intro run hrun
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support run
    · rw [hreads (cells, pad) z.1 (hrun z hz)]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  rw [hconv _ fun z hz => value_mem_support _ _ _ z hz,
    hconv _ fun z hz => value_mem_support _ _ _ z hz]
  exact (HandlerStall.expected_aiming_claimed_stalled_eq publicSeed availableAt impl hfacts
    hmono stakes index (cells, pad)
      (fun cache node => ¬ availableAt (cells, pad) cache node ∧ admitAt cache)
      (fun _ _ h => h.1) stall
      (computation (cells, pad)) state claims hcache).symm

/-! ## Summed over the cells -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **A run of the handler is charged its expected number of aiming probes.** The run reads the
table only at `touched`, and every cell there but the secret seed is available throughout, so
excluding both from the sum excludes nothing an adversary can use. The charge stops at the
expectation rather than at a cap, so that the halves sharing a budget add pathwise. -/
theorem prob_sensitive_run_le_expected {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hopen : ∀ (value : α) (node : CanonicalGraph.Node), touched node →
      node ≠ CanonicalGraph.Node.secretSeed →
        ∀ cache : HandlerCarrier.State, ¬ unavailableOf value cache node)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool) (weight : α × (HandlerState × Bool) → Nat)
    (hweight : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state),
      ∑ index : CanonicalGraph.Node, ChargedProbe.aiming stakes
        (unavailableOf z.1) index z.2.1.2.1.dedup ≤ weight z) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveOffSeed stakes
          (unavailableOf pair.1.1) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
          ((weight z : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono
    (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
      ∃ index ∈ (Finset.univ : Finset CanonicalGraph.Node),
        ¬ touched index ∧ ∃ entry ∈ pair.1.2.1.2.1,
          ChargedBy stakes (unavailableOf pair.1.1) index
            (pair.2 index) entry) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    obtain ⟨index, hne, node, hstake, hunavailable, hinput⟩ :=
      (RedrawCell.sensitiveOffSeed_iff_exists stakes
        (unavailableOf pair.1.1) pair.2 entry.2 entry.1).mp hsensitive
    refine ⟨index, ?_, fun htouch => hopen pair.1.1 index htouch hne entry.2 hunavailable,
      entry, hentry, node, hstake, hunavailable, hinput⟩
    simp
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  have hindex : ∀ index : CanonicalGraph.Node,
      Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
          ¬ touched index ∧ ∃ entry ∈ pair.1.2.1.2.1,
            ChargedBy stakes (unavailableOf pair.1.1) index
              (pair.2 index) entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (impl (cells, pad)))
            (computation (cells, pad))).run state
          pure (result, cells))] ≤
        (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
            ((aiming stakes (unavailableOf z.1) index z.2.1.2.1.dedup : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    intro index
    by_cases hi : touched index
    · refine le_trans (probEvent_mono (q := fun _ => False)
        (fun pair _ hpair => hpair.1 hi)) ?_
      simp
    refine le_trans (probEvent_mono
      (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
          (unavailableOf pair.1.1) index (pair.2 index) entry)
      (fun pair _ hpair => hpair.2)) ?_
    refine le_trans (le_of_eq ?_)
      (prob_charged_index_le publicSeed availableAt impl hfacts hmono stakes index touched hi
        hcover stall computation htouched admitAt unavailableOf hreads state)
    have hmapped : (fun pair : (α × (HandlerState × Bool)) × Cells =>
          (pair.1, pair.2 index)) <$> (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            let result ← (simulateQ (withFlag (impl (cells, pad)))
              (computation (cells, pad))).run state
            pure (result, cells)) =
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (impl (cells, pad)))
            (computation (cells, pad))).run state
          pure (result, cells index)) := by
      simp only [map_bind, bind_pure_comp, Functor.map_map]
    rw [← hmapped, probEvent_map]
    rfl
  refine le_trans (Finset.sum_le_sum fun index _ => hindex index) ?_
  have hsum := ChargedProbe.sum_weighted_le_of_sum_indexed stakes
    (fun z : α × (HandlerState × Bool) => unavailableOf z.1)
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)
    (fun z => z.2.1.2.1.dedup) weight hweight
  exact hsum

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The claims a run returns are charged their expected number too**, with the record
replaced by a list the run's value determines. -/
theorem prob_claimed_run_le_expected {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hopen : ∀ (value : α) (node : CanonicalGraph.Node), touched node →
      node ≠ CanonicalGraph.Node.secretSeed →
        ∀ cache : HandlerCarrier.State, ¬ unavailableOf value cache node)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool)
    (claims : α × (HandlerState × Bool) → List (Bytes × HandlerCarrier.State))
    (hcache : ∀ (z : α × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State),
      entry ∈ claims z → entry.2 = z.2.1.1) (weight : α × (HandlerState × Bool) → Nat)
    (hweight : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state),
      ∑ index : CanonicalGraph.Node, ChargedProbe.aiming stakes
        (unavailableOf z.1) index (claims z).dedup ≤ weight z) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ claims pair.1, RedrawCell.SensitiveOffSeed stakes
          (unavailableOf pair.1.1) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
          ((weight z : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono
    (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
      ∃ index ∈ (Finset.univ : Finset CanonicalGraph.Node),
        ¬ touched index ∧ ∃ entry ∈ claims pair.1,
          ChargedBy stakes (unavailableOf pair.1.1) index
            (pair.2 index) entry) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    obtain ⟨index, hne, node, hstake, hunavailable, hinput⟩ :=
      (RedrawCell.sensitiveOffSeed_iff_exists stakes
        (unavailableOf pair.1.1) pair.2 entry.2 entry.1).mp hsensitive
    refine ⟨index, ?_, fun htouch => hopen pair.1.1 index htouch hne entry.2 hunavailable,
      entry, hentry, node, hstake, hunavailable, hinput⟩
    simp
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  have hindex : ∀ index : CanonicalGraph.Node,
      Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
          ¬ touched index ∧ ∃ entry ∈ claims pair.1,
            ChargedBy stakes (unavailableOf pair.1.1) index
              (pair.2 index) entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (impl (cells, pad)))
            (computation (cells, pad))).run state
          pure (result, cells))] ≤
        (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
            ((aiming stakes (unavailableOf z.1) index (claims z).dedup : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    intro index
    by_cases hi : touched index
    · refine le_trans (probEvent_mono (q := fun _ => False)
        (fun pair _ hpair => hpair.1 hi)) ?_
      simp
    refine le_trans (probEvent_mono
      (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ claims pair.1, ChargedBy stakes
          (unavailableOf pair.1.1) index (pair.2 index) entry)
      (fun pair _ hpair => hpair.2)) ?_
    refine le_trans (le_of_eq ?_)
      (prob_claimed_index_le publicSeed availableAt impl hfacts hmono stakes index touched hi
        hcover stall computation htouched admitAt unavailableOf hreads state claims hcache)
    have hmapped : (fun pair : (α × (HandlerState × Bool)) × Cells =>
          (pair.1, pair.2 index)) <$> (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            let result ← (simulateQ (withFlag (impl (cells, pad)))
              (computation (cells, pad))).run state
            pure (result, cells)) =
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (impl (cells, pad)))
            (computation (cells, pad))).run state
          pure (result, cells index)) := by
      simp only [map_bind, bind_pure_comp, Functor.map_map]
    rw [← hmapped, probEvent_map]
    rfl
  refine le_trans (Finset.sum_le_sum fun index _ => hindex index) ?_
  have hsum := ChargedProbe.sum_weighted_le_of_sum_indexed stakes
    (fun z : α × (HandlerState × Bool) => unavailableOf z.1)
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)
    (fun z => (claims z).dedup) weight hweight
  exact hsum

/-! ## The two caps -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The claims cost their own number**, which is a constant per run and so its own
expectation. -/
theorem prob_claimed_run_le {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hopen : ∀ (value : α) (node : CanonicalGraph.Node), touched node →
      node ≠ CanonicalGraph.Node.secretSeed →
        ∀ cache : HandlerCarrier.State, ¬ unavailableOf value cache node)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool)
    (claims : α × (HandlerState × Bool) → List (Bytes × HandlerCarrier.State))
    (hcache : ∀ (z : α × (HandlerState × Bool)) (entry : Bytes × HandlerCarrier.State),
      entry ∈ claims z → entry.2 = z.2.1.1) (limit : Nat)
    (hlength : ∀ z : α × (HandlerState × Bool), (claims z).length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ claims pair.1, RedrawCell.SensitiveOffSeed stakes
          (unavailableOf pair.1.1) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans
    (prob_claimed_run_le_expected publicSeed availableAt impl hfacts hmono stakes stall
      computation touched hcover htouched admitAt unavailableOf hopen hreads state claims hcache
      (fun z => (claims z).length)
      fun z _ => le_trans (ChargedProbe.sum_targets_length_le stakes
        (unavailableOf z.1) (claims z).dedup)
        (List.Sublist.length_le (List.dedup_sublist _)))
    (ChargedProbe.tsum_weight_le _
      (fun z : α × (HandlerState × Bool) => (claims z).length) limit fun z _ => hlength z)

open scoped Classical in
/-- **The same charge, capped at the record's length.** -/
theorem prob_sensitive_run_le {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stakes : Stakes Target CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hopen : ∀ (value : α) (node : CanonicalGraph.Node), touched node →
      node ≠ CanonicalGraph.Node.secretSeed →
        ∀ cache : HandlerCarrier.State, ¬ unavailableOf value cache node)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool) (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state),
      z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveOffSeed stakes
          (unavailableOf pair.1.1) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans
    (prob_sensitive_run_le_expected publicSeed availableAt impl hfacts hmono stakes stall
      computation touched hcover htouched admitAt unavailableOf hopen hreads state
      (fun z => z.2.1.2.1.length)
      fun z _ => le_trans (ChargedProbe.sum_targets_length_le stakes
        (unavailableOf z.1) z.2.1.2.1.dedup)
        (List.Sublist.length_le (List.dedup_sublist _)))
    (ChargedProbe.tsum_weight_le _
      (fun z : α × (HandlerState × Bool) => z.2.1.2.1.length) limit hlimit)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The charge at the record's canonical part**, which is the count the shared budget grants
this half: a whole class of inputs rather than a share of one, left at its expectation so that
the charges sharing the budget can be added. The probes are counted distinctly. -/
theorem prob_sensitive_run_le_canonical {α : Type} (publicSeed : Digest)
    (availableAt : Cells × Padding → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (impl : Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {allowed : CanonicalGraph.Node → Prop}
    (hfacts : TableFacts publicSeed availableAt allowed impl)
    (hmono : ∀ (table : Cells × Padding) (left right : HandlerCarrier.State),
      HandlerCarrier.Grows left right →
        ∀ node, availableAt table left node → availableAt table right node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (admitAt : HandlerCarrier.State → Prop)
    (unavailableOf : α → HandlerCarrier.State → CanonicalGraph.Node → Prop)
    (hopen : ∀ (value : α) (node : CanonicalGraph.Node), touched node →
      node ≠ CanonicalGraph.Node.secretSeed →
        ∀ cache : HandlerCarrier.State, ¬ unavailableOf value cache node)
    (hreads : ∀ (table : Cells × Padding) (value : α), value ∈ support (computation table) →
      unavailableOf value = fun cache node => ¬ availableAt table cache node ∧ admitAt cache)
    (state : HandlerState × Bool) (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveOffSeed (GraphStakes.stakes publicSeed)
          (unavailableOf pair.1.1) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (impl (cells, pad)))
          (computation (cells, pad))).run state
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (impl (cells, pad))) (computation (cells, pad))).run state)] *
          (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  prob_sensitive_run_le_expected publicSeed availableAt impl hfacts hmono
    (GraphStakes.stakes publicSeed) stall computation touched hcover htouched admitAt
    unavailableOf hopen hreads state
    (fun z => (z.2.1.2.1.dedup.filter keep).length)
    fun z _ => RedrawCell.sum_aiming_le_canonical publicSeed
      (unavailableOf z.1) keep hkeep z.2.1.2.1.dedup

end SlhDsaSecurity.HandlerCharge

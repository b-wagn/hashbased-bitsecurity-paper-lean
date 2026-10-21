import SlhDsaSecurity.Proof.ChargedProbe
import SlhDsaSecurity.Proof.LazyBridge

/-!
# A cell a run cannot read may be drawn after it

`ChargedProbe.prob_run_sensitive_le` charges a run one unit of `2 ^ -128` per probe, with the
cell it is charged against drawn *after* the run. `OpenCache.evalDist_stalled_lazyProgram_congr`
offers something weaker in form though equal in content: the run's law is unchanged by altering
that cell, a congruence rather than a factorisation.

`evalDist_redraw_coordinate` converts the one into the other. If altering one coordinate of the
cell table leaves a run's law alone, then the joint law of the run's result and that coordinate
is the same as the law of the result together with an *independently* drawn cell — the
coordinate may be redrawn. `evalDist_uniformSample_bind_update` is what makes it
short: a uniform table is a uniform table with one coordinate overwritten by a fresh uniform
value, so the overwriting value can be substituted for the coordinate everywhere and then
commuted past the run.

Only the cell is freed, not the padding of its node. That is a *stronger* hypothesis than
`OpenCache.AgreeOff`, so the congruence supplies it directly, and it keeps the statement about
the cell table alone with everything else carried along as auxiliary randomness.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.RedrawCell

open CanonicalGraph SensitiveQuery

/-- **A coordinate a run cannot read may be redrawn.** -/
theorem evalDist_redraw_coordinate {γ Aux : Type} (index : CanonicalGraph.Node)
    (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp γ)
    (hcongr : ∀ (cells other : Cells) (aux : Aux),
      (∀ node, node ≠ index → cells node = other node) →
        𝒟[run cells aux] = 𝒟[run other aux]) :
    𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
  classical
  have hupdate := evalDist_uniformSample_bind_update
    (D := CanonicalGraph.Node) (R := Cell) index
  calc 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells index)]
      = 𝒟[(do
            let cell ← ($ᵗ Cell : ProbComp Cell)
            let cells ← ($ᵗ Cells : ProbComp Cells)
            pure (Function.update cells index cell)) >>= fun cells => do
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cells index)] :=
        (LazyBridge.evalDist_bind_congr_right hupdate _).symm
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run (Function.update cells index cell) aux
          pure (result, cell)] := by
        simp only [bind_assoc, pure_bind, Function.update_self]
    _ = 𝒟[do
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cell => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        refine LazyBridge.evalDist_bind_congr_right ?_ _
        exact hcongr _ _ aux fun node hnode => Function.update_of_ne hnode _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cell)] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let cell ← ($ᵗ Cell : ProbComp Cell)
          let result ← run cells aux
          pure (result, cell)] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun cells => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun aux => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _


/-! ## The charge against the joint draw

With the coordinate redrawn, the per-cell charge applies to the run itself. Summed over the
cells it comes to one unit per probe, the weights adding to the probe count. -/

open ChargedProbe

variable {Target : Type}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **A run that reads no cell it is charged against is charged one unit per probe.**

Read the hypothesis carefully: `hcongr` asks for blindness at *every* cell of one and the same
run. Any two cell tables differ at finitely many coordinates, so chaining it makes such a run
independent of the table altogether. It is therefore the statement for a run that reads no cell
at all, not for one that reads the available cells — a handler that reads those is blind to a
given cell only while that cell is unavailable, which is blindness of a *different* run for
each cell, the one stalled at that cell.

Carrying the weighting across that difference needs the expected counts to be taken under the
real run rather than under each stalled one, which is a further step and not this lemma. -/
theorem prob_joint_sensitive_le {γ Aux : Type} (stakes : Stakes Target CanonicalGraph.Node)
    (unavailable : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp γ)
    (record : γ → List (Bytes × QueryCache HashSpec)) (limit : Nat)
    (hcongr : ∀ (index : CanonicalGraph.Node) (cells other : Cells) (aux : Aux),
      (∀ node, node ≠ index → cells node = other node) →
        𝒟[run cells aux] = 𝒟[run other aux])
    (hlimit : ∀ (cells : Cells) (aux : Aux), ∀ result ∈ support (run cells aux),
      (record result).length ≤ limit) :
    Pr[fun pair : γ × Cells =>
        ∃ entry ∈ record pair.1, Sensitive stakes unavailable pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun pair : γ × Cells =>
    ∃ index ∈ (Finset.univ : Finset CanonicalGraph.Node), ∃ entry ∈ record pair.1,
      ChargedBy stakes unavailable index (pair.2 index) entry) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    obtain ⟨index, hcharged⟩ :=
      (sensitive_iff_exists stakes unavailable pair.2 entry.2 entry.1).mp hsensitive
    refine ⟨index, ?_, entry, hentry, hcharged⟩
    simp
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  -- Each cell's charge is read off the result and that cell alone, which may be redrawn.
  have hcoordinate : ∀ index : CanonicalGraph.Node,
      Pr[fun pair : γ × Cells =>
          ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index (pair.2 index) entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cells))] =
        Pr[fun pair : γ × Cell =>
            ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
          (do
            let result ← (do
              let cells ← ($ᵗ Cells : ProbComp Cells)
              let aux ← auxiliary
              run cells aux)
            let cell ← ($ᵗ Cell : ProbComp Cell)
            pure (result, cell))] := by
    intro index
    have hmap : Pr[fun pair : γ × Cells =>
        ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index (pair.2 index) entry |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run cells aux
        pure (result, cells))] =
      Pr[fun pair : γ × Cell =>
          ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let aux ← auxiliary
          let result ← run cells aux
          pure (result, cells index))] := by
      have hmapped : (fun pair : γ × Cells => (pair.1, pair.2 index)) <$> (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let aux ← auxiliary
            let result ← run cells aux
            pure (result, cells)) =
          (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let aux ← auxiliary
            let result ← run cells aux
            pure (result, cells index)) := by
        simp only [map_bind, bind_pure_comp, Functor.map_map]
      rw [← hmapped, probEvent_map]
      rfl
    rw [hmap]
    refine probEvent_congr' (fun _ _ => Iff.rfl) ?_
    refine (evalDist_redraw_coordinate index auxiliary run (hcongr index)).trans ?_
    simp only [bind_assoc]
  simp only [hcoordinate]
  refine prob_run_sensitive_le stakes unavailable _ record limit fun result hresult => ?_
  rw [mem_support_bind_iff] at hresult
  obtain ⟨cells, -, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨aux, -, hrun⟩ := hrest
  exact hlimit cells aux result hrun


/-! ## The charge against one cell, at the game's handler

The three pieces meet here. Stalling at the cell leaves the chance of a charge against it
alone; the stalled run does not read that cell, so it may be drawn after; and the weight the
drawn cell costs is the number of probes aiming at it, which stalling also leaves alone. -/

open OpenCache ChargedProbe

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The charge against one cell.** -/
theorem prob_charged_index_le {α : Type} (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hclosed : ∀ (cache : QueryCache HashSpec) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt cache child) →
        availableAt cache (.structural parent))
    (hmono : ∀ (left right : QueryCache HashSpec), CacheAvailability.Persists left right →
      ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Target CanonicalGraph.Node) (index : CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
        ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
          (fun cache node => ¬ availableAt cache node) index pair.2 entry |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          computation).run state
        pure (result, cells index))] ≤
      (∑' z : α × (HandlerState × Bool),
        Pr[= z | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
            computation).run state)] *
          ((aiming stakes (fun cache node => ¬ availableAt cache node) index z.2.1.2.1 :
            Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  -- Stalling at the cell leaves the chance of a charge against it alone.
  have hstall : Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
      ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
        (fun cache node => ¬ availableAt cache node) index pair.2 entry |
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
        computation).run state
      pure (result, cells index))] =
      Pr[fun pair : (α × (HandlerState × Bool)) × Cell =>
          ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt cache node) index pair.2 entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (StalledRun.stalled
            (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
            (fun inner => availableAt inner.1 index) stall) computation).run state
          pure (result, cells index))] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun cells => congrArg _ ?_
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun pad => congrArg _ ?_
    rw [bind_pure_comp, probEvent_map, bind_pure_comp, probEvent_map]
    exact prob_charged_stalled_eq publicSeed availableAt hmono stakes index (cells, pad) stall
      computation state
  -- The stalled run does not read that cell, so it may be drawn after.
  have hredraw : 𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled
          (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          (fun inner => availableAt inner.1 index) stall) computation).run state
        pure (result, cells index)] =
      𝒟[do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled
          (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          (fun inner => availableAt inner.1 index) stall) computation).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)] := by
    refine evalDist_redraw_coordinate index ($ᵗ Padding : ProbComp Padding) _ ?_
    intro cells other pad hagree
    exact evalDist_stalled_lazyProgram_congr publicSeed availableAt hclosed index
      (cells, pad) (other, pad) ⟨hagree, fun parent _ => rfl⟩ stall computation state
  rw [hstall, probEvent_congr' (fun _ _ => Iff.rfl) hredraw]
  -- The drawn cell costs the probes aiming at it, and stalling leaves their number alone.
  have hassoc : (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (StalledRun.stalled
          (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          (fun inner => availableAt inner.1 index) stall) computation).run state
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) =
      (do
        let result ← (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          (simulateQ (StalledRun.stalled
            (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
            (fun inner => availableAt inner.1 index) stall) computation).run state)
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell)) := by
    simp only [bind_assoc]
  rw [hassoc]
  refine le_trans (prob_run_cell_le stakes
    (fun cache node => ¬ availableAt cache node) index
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (StalledRun.stalled
        (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
        (fun inner => availableAt inner.1 index) stall) computation).run state)
    (fun z => z.2.1.2.1)) ?_
  refine ENNReal.div_le_div_right (le_of_eq ?_) _
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  refine tsum_congr fun pad => congrArg _ ?_
  exact (expected_aiming_stalled_eq publicSeed availableAt hmono stakes index (cells, pad)
    stall computation state).symm


/-! ## The input half's charge

Summed over the cells. Each cell's charge is weighted by the probes aiming at it, those weights
add to the number of probes, and the sum over cells meets the expectation over runs through
`ChargedProbe.sum_tsum_comm`. What is left is the four things the game supplies: closure of
availability under the structure, its monotonicity in the cache, a bound on the recorded
probes, and the stakes structure. -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **A run of the handler that answers only what it may is charged one unit per probe.** -/
theorem prob_sensitive_run_le {α : Type} (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop)
    (hclosed : ∀ (cache : QueryCache HashSpec) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt cache child) →
        availableAt cache (.structural parent))
    (hmono : ∀ (left right : QueryCache HashSpec), CacheAvailability.Persists left right →
      ∀ node, availableAt left node → availableAt right node)
    (stakes : Stakes Target CanonicalGraph.Node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (state : HandlerState × Bool) (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          computation).run state), z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
        ∃ entry ∈ pair.1.2.1.2.1, Sensitive stakes
          (fun cache node => ¬ availableAt cache node) pair.2 entry.2 entry.1 |
      (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
          computation).run state
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono
    (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
      ∃ index ∈ (Finset.univ : Finset CanonicalGraph.Node), ∃ entry ∈ pair.1.2.1.2.1,
        ChargedBy stakes (fun cache node => ¬ availableAt cache node) index
          (pair.2 index) entry) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    obtain ⟨index, hcharged⟩ :=
      (sensitive_iff_exists stakes (fun cache node => ¬ availableAt cache node) pair.2
        entry.2 entry.1).mp hsensitive
    refine ⟨index, ?_, entry, hentry, hcharged⟩
    simp
  refine le_trans (probEvent_exists_finset_le_sum _ _ _) ?_
  -- Each cell's charge reads the result and that cell alone.
  have hindex : ∀ index : CanonicalGraph.Node,
      Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
          ∃ entry ∈ pair.1.2.1.2.1, ChargedBy stakes
            (fun cache node => ¬ availableAt cache node) index (pair.2 index) entry |
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
            computation).run state
          pure (result, cells))] ≤
        (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
              computation).run state)] *
            ((aiming stakes (fun cache node => ¬ availableAt cache node) index z.2.1.2.1 :
              Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    intro index
    refine le_trans (le_of_eq ?_)
      (prob_charged_index_le publicSeed availableAt hclosed hmono stakes index stall
        computation state)
    have hmapped : (fun pair : (α × (HandlerState × Bool)) × Cells =>
          (pair.1, pair.2 index)) <$> (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
              computation).run state
            pure (result, cells)) =
        (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
            computation).run state
          pure (result, cells index)) := by
      simp only [map_bind, bind_pure_comp, Functor.map_map]
    rw [← hmapped, probEvent_map]
    rfl
  refine le_trans (Finset.sum_le_sum fun index _ => hindex index) ?_
  exact ChargedProbe.sum_weighted_le stakes (fun cache node => ¬ availableAt cache node)
    (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      (simulateQ (withFlag (lazyProgram publicSeed availableAt (cells, pad)))
        computation).run state)
    (fun z => z.2.1.2.1) limit hlimit

/-! ## The game's run is this one with the record forgotten

The charge is about a handler that keeps a record; a game's run has no record. At total
availability the two are the same run. The handler answers from the table at every canonical
input, and the game's cache already holds those entries — the walk programmed them there — so
the handler's table branch is never reached, and what is left is the shared oracle with a
record alongside. Forgetting the record gives the game's run back.

Nothing about the walk's distribution is used, only that its cache carries the canonical
entries. There is no order condition and no deferred sampling: the equality is step by step. -/

/-- What one query leaves in the record and the count. -/
def restamp (queried : OracleWorld.Domain)
    (record : List (Bytes × QueryCache HashSpec)) (count : Nat)
    (cache : QueryCache HashSpec) : List (Bytes × QueryCache HashSpec) × Nat :=
  match queried with
  | Sum.inl _ => (record, count)
  | Sum.inr input => (record ++ [(input, cache)], count + 1)

/-- **The shared oracle only ever adds to its cache.** -/
theorem rom_persists (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (step : OracleWorld.Range queried × QueryCache HashSpec)
    (hstep : step ∈ support ((KeygenUniform.rom queried).run cache)) :
    CacheAvailability.Persists cache step.2 := by
  classical
  rcases queried with coin | input
  · rw [DigestTape.rom_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact CacheAvailability.Persists.refl _
  · rw [DigestTape.rom_run_inr] at hstep
    cases hcached : cache input with
    | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
        Set.mem_singleton_iff] at hstep
      rw [hstep]
      exact CacheAvailability.Persists.refl _
    | none =>
      rw [QueryImpl.withCaching_run_none _ hcached] at hstep
      simp only [uniformSampleImpl, map_eq_bind_pure_comp, mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [hpure]
      exact CacheAvailability.persists_cacheQuery cache input answer hcached

open scoped Classical in
/-- **At total availability the handler is the shared oracle with a record alongside.** -/
theorem lazyProgram_total_run (publicSeed : Digest) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (record : List (Bytes × QueryCache HashSpec)) (count : Nat)
    (hprog : CacheAvailability.Persists (openCache publicSeed (fun _ => True) table) cache) :
    ((lazyProgram publicSeed (fun _ _ => True) table) queried).run (cache, record, count) =
      (fun z : OracleWorld.Range queried × QueryCache HashSpec =>
          (z.1, (z.2, restamp queried record count cache))) <$>
        (KeygenUniform.rom queried).run cache := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, DigestTape.rom_run_inl]
    simp [restamp, map_eq_bind_pure_comp, bind_assoc]
  · rw [lazyProgram_run_inr, DigestTape.rom_run_inr]
    cases hcached : cache input with
    | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcached]
      simp only [hcached, restamp, pure_bind, map_pure]
    | none =>
      have hnone : openCache publicSeed (fun _ => True) table input = none := by
        cases hopen : openCache publicSeed (fun _ => True) table input with
        | none => rfl
        | some answer =>
          rw [hprog input answer hopen] at hcached
          exact absurd hcached (by simp)
      rw [QueryImpl.withCaching_run_none _ hcached]
      simp only [hcached, hnone, restamp, uniformSampleImpl, map_eq_bind_pure_comp,
        bind_assoc, Function.comp_apply, pure_bind]

open scoped Classical in
/-- **The game's run is the handler's run with the record forgotten.** -/
theorem probEvent_rom_eq_lazyProgram {α : Type} (publicSeed : Digest) (table : Cells × Padding)
    (event : α × QueryCache HashSpec → Prop) (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (record : List (Bytes × QueryCache HashSpec)) (count : Nat),
      CacheAvailability.Persists (openCache publicSeed (fun _ => True) table) cache →
        Pr[event | (simulateQ KeygenUniform.rom computation).run cache] =
          Pr[fun z : α × HandlerState => event (z.1, z.2.1) |
            (simulateQ (lazyProgram publicSeed (fun _ _ => True) table) computation).run
              (cache, record, count)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache record count _
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure,
      probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    intro cache record count hprog
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      lazyProgram_total_run publicSeed table queried cache record count hprog,
      bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun step => ?_
    by_cases hmem : step ∈ support ((KeygenUniform.rom queried).run cache)
    · exact congrArg _ (ih step.1 step.2 _ _
        (CacheAvailability.Persists.trans hprog (rom_persists queried cache step hmem)))
    · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-! ## The programmed cache read on demand

The run above starts from the game's cache, which already carries the cells, so the charge —
which is about a run blind to them — cannot be read off it. What the charge wants is the handler
started from nothing, drawing the programmed entries only as they are asked for.

That run is the game's run too. At total availability the handler serves exactly the entries the
walk programmed, so at every moment the game's cache is the programmed entries with whatever the
handler has drawn beside them, and the two answer every query alike. The relation between the
two caches is an equation, not a coupling: `unionCache` says what the game holds while the
handler holds its own, and one induction carries it. -/

/-- The programmed entries, with whatever the handler has drawn beside them. -/
noncomputable def unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input =>
    match openCache publicSeed (fun _ => True) table input with
    | some answer => some answer
    | none => cache input

theorem unionCache_of_open (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes) (answer : HashOutput)
    (hopen : openCache publicSeed (fun _ => True) table input = some answer) :
    unionCache publicSeed table cache input = some answer := by
  rw [unionCache, hopen]

theorem unionCache_of_none (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hopen : openCache publicSeed (fun _ => True) table input = none) :
    unionCache publicSeed table cache input = cache input := by
  rw [unionCache, hopen]

/-- **Caching what the table already said changes nothing the game can see.** -/
theorem unionCache_cacheQuery_open (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes) (answer : HashOutput)
    (hopen : openCache publicSeed (fun _ => True) table input = some answer) :
    unionCache publicSeed table (cache.cacheQuery input answer) =
      unionCache publicSeed table cache := by
  funext probe
  by_cases hprobe : probe = input
  · subst hprobe
    rw [unionCache_of_open publicSeed table _ probe answer hopen,
      unionCache_of_open publicSeed table cache probe answer hopen]
  · rw [unionCache, unionCache, QueryCache.cacheQuery_of_ne _ _ hprobe]

/-- **A fresh answer lands in both caches alike.** -/
theorem unionCache_cacheQuery_fresh (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hopen : openCache publicSeed (fun _ => True) table input = none) (answer : HashOutput) :
    unionCache publicSeed table (cache.cacheQuery input answer) =
      (unionCache publicSeed table cache).cacheQuery input answer := by
  funext probe
  by_cases hprobe : probe = input
  · subst hprobe
    rw [unionCache_of_none publicSeed table _ probe hopen, QueryCache.cacheQuery_self,
      QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hprobe]
    simp only [unionCache, QueryCache.cacheQuery_of_ne _ _ hprobe]

/-- A handler cache saying nothing the programmed entries contradict. -/
def Compatible (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) : Prop :=
  CacheAvailability.Persists cache (unionCache publicSeed table cache)

theorem compatible_empty (publicSeed : Digest) (table : Cells × Padding) :
    Compatible publicSeed table ∅ := by
  intro probe value hprobe
  simp at hprobe

open scoped Classical in
/-- **The game's step is the handler's step, read through the union.** -/
theorem rom_union_step (publicSeed : Digest) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (record : List (Bytes × QueryCache HashSpec)) (count : Nat)
    (hcompat : Compatible publicSeed table cache) :
    (KeygenUniform.rom queried).run (unionCache publicSeed table cache) =
      (fun z : OracleWorld.Range queried × HandlerState =>
          (z.1, unionCache publicSeed table z.2.1)) <$>
        ((lazyProgram publicSeed (fun _ _ => True) table) queried).run
          (cache, record, count) := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, DigestTape.rom_run_inl]
    simp [map_eq_bind_pure_comp, bind_assoc]
  · rw [lazyProgram_run_inr, DigestTape.rom_run_inr]
    cases hcached : cache input with
    | some cached =>
      rw [QueryImpl.withCaching_run_some _ (hcompat input cached hcached)]
      simp only [hcached, pure_bind, map_pure]
    | none =>
      cases hopen : openCache publicSeed (fun _ => True) table input with
      | some answer =>
        rw [QueryImpl.withCaching_run_some _
          (unionCache_of_open publicSeed table cache input answer hopen)]
        simp only [hcached, pure_bind, map_pure,
          unionCache_cacheQuery_open publicSeed table cache input answer hopen]
      | none =>
        rw [QueryImpl.withCaching_run_none _
          (by rw [unionCache_of_none publicSeed table cache input hopen, hcached])]
        simp only [hcached, uniformSampleImpl, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply, pure_bind,
          unionCache_cacheQuery_fresh publicSeed table cache input hopen]
        rfl

open scoped Classical in
/-- **The handler's cache stays compatible with the table.** -/
theorem compatible_step (publicSeed : Digest) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (record : List (Bytes × QueryCache HashSpec)) (count : Nat)
    (hcompat : Compatible publicSeed table cache)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed (fun _ _ => True) table)
      queried).run (cache, record, count))) :
    Compatible publicSeed table step.2.1 := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1 = cache from by rw [hpure]]
    exact hcompat
  · have hbind : step ∈ support
        (LazyBudget.lazyAnswer publicSeed (fun _ _ => True) table input cache >>= fun inner =>
          (pure (inner.1, (inner.2, record ++ [(input, cache)], count + 1)) :
            ProbComp (HashOutput × HandlerState))) := hstep
    rw [mem_support_bind_iff] at hbind
    obtain ⟨inner, hinner, hpure⟩ := hbind
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2.1 = inner.2 from by rw [hpure]]
    rw [LazyBudget.lazyAnswer] at hinner
    cases hcached : cache input with
    | some cached =>
      rw [hcached, support_pure, Set.mem_singleton_iff] at hinner
      rw [show inner.2 = cache from by rw [hinner]]
      exact hcompat
    | none =>
      rw [hcached] at hinner
      cases hopen : openCache publicSeed (fun _ => True) table input with
      | some answer =>
        rw [hopen, support_pure, Set.mem_singleton_iff] at hinner
        rw [show inner.2 = cache.cacheQuery input answer from by rw [hinner]]
        intro probe value hvalue
        rw [unionCache_cacheQuery_open publicSeed table cache input answer hopen]
        by_cases hprobe : probe = input
        · subst hprobe
          rw [QueryCache.cacheQuery_self] at hvalue
          rw [unionCache_of_open publicSeed table cache probe answer hopen, hvalue]
        · rw [QueryCache.cacheQuery_of_ne _ _ hprobe] at hvalue
          exact hcompat probe value hvalue
      | none =>
        rw [hopen, support_map] at hinner
        obtain ⟨answer, -, heq⟩ := hinner
        rw [show inner.2 = cache.cacheQuery input answer from by rw [← heq]]
        intro probe value hvalue
        rw [unionCache_cacheQuery_fresh publicSeed table cache input hopen]
        by_cases hprobe : probe = input
        · subst hprobe
          rw [QueryCache.cacheQuery_self] at hvalue
          rw [QueryCache.cacheQuery_self, hvalue]
        · rw [QueryCache.cacheQuery_of_ne _ _ hprobe] at hvalue
          rw [QueryCache.cacheQuery_of_ne _ _ hprobe]
          exact hcompat probe value hvalue

open scoped Classical in
/-- **The game's run is the handler's run at total availability.** The handler starts from
nothing, so the charge applies to it; the game starts from the programmed cache. -/
theorem probEvent_rom_eq_lazy {α : Type} (publicSeed : Digest) (table : Cells × Padding)
    (event : α × QueryCache HashSpec → Prop) (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (record : List (Bytes × QueryCache HashSpec)) (count : Nat),
      Compatible publicSeed table cache →
        Pr[event | (simulateQ KeygenUniform.rom computation).run
            (unionCache publicSeed table cache)] =
          Pr[fun z : α × HandlerState => event (z.1, unionCache publicSeed table z.2.1) |
            (simulateQ (lazyProgram publicSeed (fun _ _ => True) table) computation).run
              (cache, record, count)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache record count _
    rw [simulateQ_pure, StateT.run_pure, simulateQ_pure, StateT.run_pure,
      probEvent_pure, probEvent_pure]
  | query_bind queried next ih =>
    intro cache record count hcompat
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      rom_union_step publicSeed table queried cache record count hcompat,
      bind_map_left, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun step => ?_
    by_cases hmem : step ∈ support (((lazyProgram publicSeed (fun _ _ => True) table)
        queried).run (cache, record, count))
    · exact congrArg _ (ih step.1 step.2.1 step.2.2.1 step.2.2.2
        (compatible_step publicSeed table queried cache record count hcompat step hmem))
    · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-! ## The charge, at the presentation the game gives

Everything the two halves need is in place, so they join. The flag the comparison carries is a
function of the record; the record's entries name nodes the charge's stakes already cover; and
the wrapper the charge is proved about differs from the comparison's only in what it writes to
that flag. What comes out is one bound on the game's own presentation — the handler at total
availability, which `probEvent_rom_eq_lazy` identifies with the game's run — with the record and
its limit left as parameters. -/

/-- **A per-table equality lifts through the draw of the table.** -/
theorem probEvent_table_congr {α : Type} (left right : Cells × Padding → ProbComp α)
    (pleft pright : α × Cells → Prop)
    (hstep : ∀ (cells : Cells) (pad : Padding),
      Pr[fun z => pleft (z, cells) | left (cells, pad)] =
        Pr[fun z => pright (z, cells) | right (cells, pad)]) :
    Pr[pleft | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let z ← left (cells, pad)
        pure (z, cells))] =
      Pr[pright | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let z ← right (cells, pad)
        pure (z, cells))] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun pad => congrArg _ ?_
  rw [show (do let z ← left (cells, pad); pure (z, cells)) =
      (fun z => (z, cells)) <$> left (cells, pad) from by rw [map_eq_bind_pure_comp]; rfl,
    show (do let z ← right (cells, pad); pure (z, cells)) =
      (fun z => (z, cells)) <$> right (cells, pad) from by rw [map_eq_bind_pure_comp]; rfl,
    probEvent_map, probEvent_map]
  exact hstep cells pad

open scoped Classical in
/-- **The comparison's flag is the charge's event.** At a state whose record is empty, the
lenient presentation flags exactly as often as the charge's wrapper records a sensitive
query. -/
theorem probEvent_flag_eq_record {α : Type} (publicSeed : Digest)
    (availableAt : QueryCache HashSpec → CanonicalGraph.Node → Prop) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) (inner : HandlerState) (hinner : inner.2.1 = []) :
    Pr[fun z : α × (HandlerState × Bool) => z.2.2 = true |
      (simulateQ (ChargedProbe.sensitiveFlagged publicSeed availableAt (fun _ _ => True) table)
        computation).run (inner, false)] =
      Pr[fun z : α × (HandlerState × Bool) => ∃ entry ∈ z.2.1.2.1,
          ChargedProbe.SensitiveEntry publicSeed availableAt table.1 entry |
        (simulateQ (withFlag (lazyProgram publicSeed availableAt table))
          computation).run (inner, false)] := by
  classical
  rw [ChargedProbe.probEvent_sensitiveFlagged_eq publicSeed availableAt table computation
      (inner, false),
    ← ChargedProbe.probEvent_sensitiveFlagged_eq_withFlag publicSeed availableAt availableAt
      table computation
      (fun z : α × HandlerState => ∃ entry ∈ z.2.2.1,
        ChargedProbe.SensitiveEntry publicSeed availableAt table.1 entry) inner false false]
  refine probEvent_congr' (fun z hz => ?_) rfl
  exact ChargedProbe.sensitiveFlagged_flag_iff_record publicSeed availableAt availableAt table
    computation (inner, false) (by simp [hinner]) z hz

open scoped Classical in
/-- **The game's presentation makes a sensitive query at most `limit / 2 ^ 128` of the time.**
The record and its limit are parameters; the availability is the signatures' own. -/
theorem prob_game_sensitive_le {α : Type} (publicSeed : Digest)
    (revealed : WotsKey → Fin chains → Nat) (hrevealed : ∀ key chain, revealed key chain ≤ w - 1)
    (signedAt : QueryCache HashSpec → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (hclosed : ∀ (cache : QueryCache HashSpec) (parent : StructuralNode),
      (∀ child ∈ parent.children,
          CanonicalGraph.Available revealed (signedAt cache) child) →
        CanonicalGraph.Available revealed (signedAt cache) (.structural parent))
    (hmono : ∀ (left right : QueryCache HashSpec), CacheAvailability.Persists left right →
      ∀ node, CanonicalGraph.Available revealed (signedAt left) node →
        CanonicalGraph.Available revealed (signedAt right) node)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : OracleComp OracleWorld α) (inner : HandlerState) (hinner : inner.2.1 = [])
    (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (lazyProgram publicSeed
          (fun cache node => CanonicalGraph.Available revealed (signedAt cache) node)
          (cells, pad))) computation).run (inner, false)), z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (ChargedProbe.sensitiveFlagged publicSeed
          (fun cache node => CanonicalGraph.Available revealed (signedAt cache) node)
          (fun _ _ => True) (cells, pad)) computation).run (inner, false)
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_table_congr
    (fun table => (simulateQ (ChargedProbe.sensitiveFlagged publicSeed
      (fun cache node => CanonicalGraph.Available revealed (signedAt cache) node)
      (fun _ _ => True) table) computation).run (inner, false))
    (fun table => (simulateQ (withFlag (lazyProgram publicSeed
      (fun cache node => CanonicalGraph.Available revealed (signedAt cache) node) table))
      computation).run (inner, false))
    _ (fun pair => ∃ entry ∈ pair.1.2.1.2.1,
      ChargedProbe.SensitiveEntry publicSeed
        (fun cache node => CanonicalGraph.Available revealed (signedAt cache) node)
        pair.2 entry)
    (fun cells pad => probEvent_flag_eq_record publicSeed _ (cells, pad) computation inner
      hinner)]
  refine le_trans (probEvent_mono (q := fun pair : (α × (HandlerState × Bool)) × Cells =>
    ∃ entry ∈ pair.1.2.1.2.1, Sensitive (GraphStakes.stakes publicSeed)
      (fun cache node => ¬ CanonicalGraph.Available revealed (signedAt cache) node)
      pair.2 entry.2 entry.1) ?_) ?_
  · rintro pair - ⟨entry, hentry, hsensitive⟩
    exact ⟨entry, hentry, ChargedProbe.sensitive_of_sensitiveEntry publicSeed revealed hrevealed
      signedAt pair.2 entry hsensitive⟩
  · exact prob_sensitive_run_le publicSeed _ hclosed hmono (GraphStakes.stakes publicSeed) stall
      computation (inner, false) limit hlimit

end SlhDsaSecurity.RedrawCell

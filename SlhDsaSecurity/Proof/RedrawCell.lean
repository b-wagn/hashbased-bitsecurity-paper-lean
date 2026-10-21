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
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
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
    (hmono : ∀ (left right : QueryCache HashSpec),
      (∀ probe, left probe ≠ none → right probe ≠ none) →
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

end SlhDsaSecurity.RedrawCell

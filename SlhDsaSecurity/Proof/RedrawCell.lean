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
/-- **A run that reads no cell it is charged against is charged one unit per probe.** The
hypothesis is the congruence the stalled handler supplies: altering one cell leaves the run's
law alone. -/
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

end SlhDsaSecurity.RedrawCell

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

open OracleComp OracleSpec

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

end SlhDsaSecurity.RedrawCell

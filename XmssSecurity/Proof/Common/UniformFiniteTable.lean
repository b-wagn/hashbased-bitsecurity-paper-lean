import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace XmssSecurity

def finHeadTailEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    evalDist (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =
    evalDist ($ᵗ (α × β)) := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

noncomputable def uniformSnocList
    (α : Type) [SampleableType α] : Nat → ProbComp (List α)
  | 0 => pure []
  | count + 1 => do
      let prior ← uniformSnocList α count
      let next ← $ᵗ α
      pure (prior ++ [next])

theorem evalDist_uniformSnocList_eq_reverse_drawList
    (α : Type) [SampleableType α] (count : Nat) :
    evalDist (uniformSnocList α count) =
      evalDist (List.reverse <$>
        OracleComp.drawList ($ᵗ α) count) := by
  induction count with
  | zero => simp [uniformSnocList, OracleComp.drawList]
  | succ count ih =>
      rw [uniformSnocList]
      calc
        _ = evalDist ((List.reverse <$>
              OracleComp.drawList ($ᵗ α) count) >>= fun prior =>
            ($ᵗ α) >>= fun next =>
            pure (prior ++ [next])) := by
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist (OracleComp.drawList ($ᵗ α) count >>= fun prior =>
            ($ᵗ α) >>= fun next =>
            pure (prior.reverse ++ [next])) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (($ᵗ α) >>= fun next =>
            OracleComp.drawList ($ᵗ α) count >>= fun prior =>
            pure (prior.reverse ++ [next])) :=
          OracleComp.DeferredSampling.evalDist_bind_comm
            (OracleComp.drawList ($ᵗ α) count) ($ᵗ α)
              (fun prior next => pure (prior.reverse ++ [next]))
        _ = evalDist (List.reverse <$>
            OracleComp.drawList ($ᵗ α) (count + 1)) := by
          simp [OracleComp.drawList, map_eq_bind_pure_comp, bind_assoc]

set_option maxRecDepth 100000 in
theorem evalDist_drawList_uniform_eq_uniformFunction
    (α : Type) [Fintype α] [SampleableType α] (count : Nat) :
    evalDist (OracleComp.drawList ($ᵗ α) count) =
      evalDist (List.ofFn <$> ($ᵗ (Fin count → α))) := by
  induction count with
  | zero =>
      rw [OracleComp.drawList]
      symm
      rw [map_eq_bind_pure_comp]
      calc
        evalDist (($ᵗ (Fin 0 → α)) >>= fun values =>
            pure (List.ofFn values)) =
            evalDist (($ᵗ (Fin 0 → α)) >>= fun _values => pure []) := by
          apply evalDist_bind_congr
          intro values _hvalues
          have hnil : List.ofFn values = [] :=
            List.eq_nil_of_length_eq_zero (by simp)
          rw [hnil]
        _ = evalDist (pure []) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            ($ᵗ (Fin 0 → α)) (probFailure_eq_zero' inferInstance) (pure [])
  | succ count ih =>
      rw [OracleComp.drawList]
      calc
        _ = evalDist (($ᵗ α) >>= fun first =>
              (List.ofFn <$> ($ᵗ (Fin count → α))) >>= fun rest =>
              pure (first :: rest)) := by
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro first
          rw [evalDist_bind, ih, ← evalDist_bind]
        _ = evalDist (List.ofFn <$> (finHeadTailEquiv α count <$> (do
              let first ← $ᵗ α
              let rest ← $ᵗ (Fin count → α)
              pure (first, rest)))) := by
          simp [finHeadTailEquiv, map_eq_bind_pure_comp, bind_assoc]
        _ = evalDist (List.ofFn <$> (finHeadTailEquiv α count <$>
              ($ᵗ (α × (Fin count → α))))) := by
          rw [evalDist_map, evalDist_map,
            evalDist_independent_uniform_pair, ← evalDist_map, ← evalDist_map]
        _ = evalDist (List.ofFn <$> ($ᵗ (Fin (count + 1) → α))) := by
          rw [evalDist_map,
            evalDist_map_bijective_uniform_cross
              (α := α × (Fin count → α))
              (β := Fin (count + 1) → α)
              (finHeadTailEquiv α count) (finHeadTailEquiv α count).bijective,
            ← evalDist_map]

noncomputable def finiteTableTapeEquiv
    {ι α : Type} [DecidableEq ι] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order) :
    (ι → α) ≃ (Fin order.length → α) :=
  (Equiv.piCongrLeft (fun _ : ι => α)
    (hnodup.getEquivOfForallMemList order hcover)).symm

noncomputable def finiteTableOfTape
    {ι α : Type} [DecidableEq ι] [Inhabited α] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order)
    (targets : List α) : ι → α :=
  if hlength : targets.length = order.length then
    (finiteTableTapeEquiv order hnodup hcover).symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    default

@[simp]
theorem finiteTableOfTape_map
    {ι α : Type} [DecidableEq ι] [Inhabited α] (order : List ι)
    (hnodup : order.Nodup) (hcover : ∀ index, index ∈ order)
    (table : ι → α) :
    finiteTableOfTape order hnodup hcover (order.map table) = table := by
  unfold finiteTableOfTape
  split
  · rename_i hlength
    apply (finiteTableTapeEquiv order hnodup hcover).injective
    rw [(finiteTableTapeEquiv order hnodup hcover).apply_symm_apply]
    funext index
    simp [finiteTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

end XmssSecurity

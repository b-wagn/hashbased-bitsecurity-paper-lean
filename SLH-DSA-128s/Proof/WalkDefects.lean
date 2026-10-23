import «SLH-DSA-128s».Proof.RandomizerGate
import «SLH-DSA-128s».Proof.WarmedGame

/-!
# The seeds' own coincidences, charged rather than assumed

Two of the charges carry a hypothesis about the key that is not a budget: that the PRF seed and
the public seed differ, which is what keeps the `PRF_msg` and canonical classes apart. Carried
as a hypothesis it is an assumption about the key; discharged it is a defect, and the defect is
one unit of `2 ^ -128` because the two seeds are drawn independently and uniformly before
anything else happens.

Discharging it is averaging over the walk, and the walk is where the seeds are drawn, so the
event is settled before the graph is traversed and before the adversary runs. That is the whole
argument: an event that reads only the walk's prefix is bounded by its probability in that
prefix, whatever happens afterwards.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WalkDefects

open Security CanonicalGraph WarmedGame

/-! ## Averaging -/

/-- **A bound that holds after every prefix holds over the bind.** -/
theorem probEvent_bind_le {α β : Type} (run : ProbComp α) (next : α → ProbComp β)
    (event : β → Prop) (bound : ℝ≥0∞) (hnext : ∀ value, Pr[event | next value] ≤ bound) :
    Pr[event | run >>= next] ≤ bound := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' value, Pr[= value | run] * Pr[event | next value]
      ≤ ∑' value, Pr[= value | run] * bound :=
        ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hnext value)
    _ = (∑' value, Pr[= value | run]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = bound := one_mul _

open scoped Classical in
/-- **An event settled by the prefix costs what it costs there.** Whatever the continuation
does, an outcome in the event comes from a prefix in the prefix's event. -/
theorem probEvent_bind_le_of_prefix {α β : Type} (run : ProbComp α) (next : α → ProbComp β)
    (event : β → Prop) (prefixEvent : α → Prop)
    (hprefix : ∀ value, ∀ result ∈ support (next value), event result → prefixEvent value) :
    Pr[event | run >>= next] ≤ Pr[prefixEvent | run] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases hvalue : prefixEvent value
  · rw [if_pos hvalue]
    calc Pr[= value | run] * Pr[event | next value]
        ≤ Pr[= value | run] * 1 := by
          refine mul_le_mul' (le_refl (Pr[= value | run])) ?_
          exact probEvent_le_one
      _ = Pr[= value | run] := mul_one _
  · rw [if_neg hvalue,
      probEvent_eq_zero fun result hresult hevent => hvalue (hprefix value result hresult hevent),
      mul_zero]

open scoped Classical in
/-- **A bound that holds after every good prefix holds over the pair, at the cost of the bad
ones.** -/
theorem probEvent_bind_pair_split_le {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : α → β → Prop) (bad : α → Prop) (bound : ℝ≥0∞)
    (hrest : ∀ value ∈ support first, ¬ bad value → Pr[event value | rest value] ≤ bound) :
    Pr[fun pair : α × β => event pair.1 pair.2 |
        (do let value ← first; let result ← rest value; pure (value, result))] ≤
      bound + Pr[bad | first] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  calc ∑' value, Pr[= value | first] *
        Pr[fun pair : α × β => event pair.1 pair.2 |
          rest value >>= fun result => pure (value, result)]
      = ∑' value, Pr[= value | first] * Pr[event value | rest value] :=
        tsum_congr fun value => congrArg _ (by rw [bind_pure_comp, probEvent_map]; rfl)
    _ ≤ ∑' value, (Pr[= value | first] * bound +
          (if bad value then Pr[= value | first] else 0)) := by
        refine ENNReal.tsum_le_tsum fun value => ?_
        by_cases hbad : bad value
        · rw [if_pos hbad]
          calc Pr[= value | first] * Pr[event value | rest value]
              ≤ Pr[= value | first] * 1 := by
                refine mul_le_mul' (le_refl (Pr[= value | first])) ?_
                exact probEvent_le_one
            _ = Pr[= value | first] := mul_one _
            _ ≤ Pr[= value | first] * bound + Pr[= value | first] := le_add_self
        · rw [if_neg hbad, add_zero]
          by_cases hmem : value ∈ support first
          · exact mul_le_mul' le_rfl (hrest value hmem hbad)
          · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = (∑' value, Pr[= value | first] * bound) +
          ∑' value, (if bad value then Pr[= value | first] else 0) := ENNReal.tsum_add
    _ ≤ bound + ∑' value, (if bad value then Pr[= value | first] else 0) := by
        gcongr
        rw [ENNReal.tsum_mul_right]
        exact le_trans (mul_le_mul' tsum_probOutput_le_one le_rfl) (le_of_eq (one_mul _))

/-! ## The seeds differ -/

/-- **The PRF seed and the public seed coincide with probability `2 ^ -128`.** -/
theorem prob_prf_eq_publicSeed_seeds :
    Pr[fun sds : Digest × Digest × Digest => sds.2.1 = sds.2.2 | seeds] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [seeds]
  refine probEvent_bind_le _ _ _ _ fun secretSeed => ?_
  refine probEvent_bind_le _ _ _ _ fun prfSeed => ?_
  rw [bind_pure_comp, probEvent_map]
  exact le_of_eq (SecretGuessCharge.prob_single_guess prfSeed)

/-- **The same at the walk**, the seeds being drawn before it traverses anything. -/
theorem prob_prf_eq_publicSeed_walk :
    Pr[fun walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec =>
        walk.1.1.2.1 = walk.1.1.2.2 | graphWalk] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [graphWalk_eq]
  refine le_trans (probEvent_bind_le_of_prefix seeds _ _
    (fun sds : Digest × Digest × Digest => sds.2.1 = sds.2.2) ?_) prob_prf_eq_publicSeed_seeds
  intro sds walk hwalk hevent
  rw [mem_support_bind_iff] at hwalk
  obtain ⟨step, -, hpure⟩ := hwalk
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure] at hevent
  exact hevent

/-! ## The public root is one of the walk's cells

The public key is the public seed and the top subtree's root, and that root is the graph's own
cell at the top `tree` node. So the pair the separation hypothesis is about is read off the
walk: one of its seeds and one of its cells.

What makes the defect `2 ^ -165` rather than the far weaker bound a fixed seed would give is
that the two are **jointly** uniform. The seed is drawn in the walk's prefix, the cell is one
coordinate of the uniform output table the traversal draws afterwards, and a coordinate of a
uniform table, truncated, is a uniform digest. Fixing the seed first and bounding the cell alone
would cost a factor of the number of address prefixes. -/

/-- The graph node whose cell is the public root: the top subtree's root. -/
def topNode : StructuralNode :=
  .tree ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩ ⟨subtreeHeight - 1, by decide⟩
    ⟨0, by decide⟩

variable [HasQuery HashSpec Id]

/-- **The public root is that cell.** -/
theorem value_topNode (secretSeed publicSeed : Digest) :
    value secretSeed publicSeed (.structural topNode) =
      Extraction.HypertreeChain.honestNode secretSeed publicSeed (layers - 1) 0 := rfl

omit [HasQuery HashSpec Id] in
/-- **A coordinate of the walk's output table, truncated, is a uniform digest.** -/
theorem outputs_coordinate_uniform (parent : StructuralNode) :
    𝒟[(fun outputs : Programming.Outputs => Hashing.truncate (outputs parent)) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  classical
  have hcoordinate : 𝒟[(fun outputs : Programming.Outputs => outputs parent) <$>
      ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)] =
      𝒟[($ᵗ HashOutput : ProbComp HashOutput)] := by
    let split : Programming.Outputs ≃ HashOutput × ({other // other ≠ parent} → HashOutput) :=
      Equiv.funSplitAt parent HashOutput
    have hmap : (fun outputs : Programming.Outputs => outputs parent) <$>
          ($ᵗ Programming.Outputs : ProbComp Programming.Outputs) =
        Prod.fst <$> (split <$> ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) := by
      rw [Functor.map_map]
      congr 1
    have hinner : 𝒟[split <$> ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)] =
        𝒟[($ᵗ (HashOutput × ({other // other ≠ parent} → HashOutput)) :
          ProbComp (HashOutput × ({other // other ≠ parent} → HashOutput)))] :=
      evalDist_map_bijective_uniform_cross (α := Programming.Outputs)
        (β := HashOutput × ({other // other ≠ parent} → HashOutput)) split split.bijective
    rw [hmap, evalDist_map, hinner, ← evalDist_map]
    exact evalDist_map_fst_uniformSample_prod
  have hcomp : (fun outputs : Programming.Outputs => Hashing.truncate (outputs parent)) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs) =
      Hashing.truncate <$> ((fun outputs : Programming.Outputs => outputs parent) <$>
        ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) := by
    rw [Functor.map_map]
  rw [hcomp, evalDist_map, hcoordinate, ← evalDist_map]
  exact KeygenUniform.truncate_uniform

omit [HasQuery HashSpec Id] in
/-- **The two halves of the public key form an address prefix with probability `2 ^ -165`.**
The seed is the walk's own and the root is one of its cells, drawn afterwards and
independently. -/
theorem prob_possible_walk :
    Pr[fun walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec =>
        HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural topNode)) | graphWalk] ≤
      1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  have hjoint : 𝒟[(do
        let seed ← ($ᵗ Digest : ProbComp Digest)
        (fun root => (seed, root)) <$> ($ᵗ Digest : ProbComp Digest))] =
      𝒟[($ᵗ (Digest × Digest) : ProbComp (Digest × Digest))] := rfl
  have hsum : ∑' publicSeed : Digest, Pr[= publicSeed | ($ᵗ Digest : ProbComp Digest)] *
        Pr[fun root : Digest => HashSeparation.Possible (publicSeed, root) |
          ($ᵗ Digest : ProbComp Digest)] ≤ 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
    refine le_trans (le_of_eq ?_) HashSeparation.prob_possible_le
    rw [← probEvent_congr' (fun _ _ => Iff.rfl) hjoint, probEvent_bind_eq_tsum]
    exact tsum_congr fun publicSeed => congrArg _ (by rw [probEvent_map]; rfl)
  rw [graphWalk_eq, seeds]
  simp only [bind_assoc, pure_bind]
  refine probEvent_bind_le _ _ _ _ fun secretSeed => ?_
  refine probEvent_bind_le _ _ _ _ fun prfSeed => ?_
  rw [probEvent_bind_eq_tsum]
  refine le_trans (le_of_eq (tsum_congr fun publicSeed => congrArg _ ?_)) hsum
  have hlaw : 𝒟[(simulateQ randomOracle
        (Programming.warmup publicSeed secretSeed)).run ∅ >>=
        fun result => pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)] =
      𝒟[((fun outputs : Programming.Outputs =>
            (Programming.cellsOfOutputs secretSeed outputs,
              Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secretSeed outputs)
                outputs Programming.order ∅)) <$>
          ($ᵗ Programming.Outputs : ProbComp Programming.Outputs)) >>=
        fun result => pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)] := by
    rw [evalDist_bind, evalDist_bind, Programming.warmup_uniform]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw, bind_map_left, bind_pure_comp, probEvent_map]
  rw [← probEvent_congr' (fun _ _ => Iff.rfl) (outputs_coordinate_uniform topNode),
    probEvent_map]
  rfl

end SlhDsaSecurity.WalkDefects

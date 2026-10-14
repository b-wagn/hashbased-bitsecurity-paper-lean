import XmssSecurity.Proof.FirstLaneEncodingExpected

/-! Expected probe accounting for hidden chain values, including probes before a reveal. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

noncomputable local instance : SampleableType (Index → Digest) :=
  SampleableType.ofFintype (Index → Digest)

def IsProbeQuery : (World Index).Domain → Prop
  | .probe _ _ => True
  | _ => False

noncomputable instance : DecidablePred (IsProbeQuery (Index := Index)) := Classical.decPred _

noncomputable def expectedDeferredProbeQueries (state : AdaptiveRevealMonitor.State Index)
    (computation : OracleComp (World Index) α) : ℝ≥0∞ :=
  ∑' base, Pr[= base | RevealProbeOracleSimulation.eagerTableSample] *
    expectedSimulatedQueryCount
      (eagerUnitImpl (RevealProbeOracleSimulation.extendTable state base))
      IsProbeQuery computation ()

theorem expected_uniformTable_update (index : Index) (weight : (Index → Digest) → ℝ≥0∞) :
    (∑' base, Pr[= base | RevealProbeOracleSimulation.eagerTableSample] * weight base) =
      ∑' value, Pr[= value | $ᵗ Digest] *
        ∑' base, Pr[= base | RevealProbeOracleSimulation.eagerTableSample] *
          weight (Function.update base index value) := by
  have hdist := evalDist_uniformSample_bind_update (R := Digest) index
  calc
    _ = ∑' base, Pr[= base | (do
          let value ← $ᵗ Digest
          let base ← RevealProbeOracleSimulation.eagerTableSample
          pure (Function.update base index value))] * weight base := by
      apply tsum_congr
      intro base
      congr 1
      exact (probOutput_congr rfl hdist).symm
    _ = _ := by
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]

omit [Fintype Index] [DecidableEq Index] in
theorem expected_eagerUnit_query_bind (table : Index → Digest)
    (predicate : (World Index).Domain → Prop) [DecidablePred predicate]
    (input : (World Index).Domain) (next : (World Index).Range input → OracleComp (World Index) α) :
    expectedSimulatedQueryCount (eagerUnitImpl table) predicate
      (liftM ((World Index).query input) >>= next) () =
      (if predicate input then 1 else 0) +
        ∑' output, Pr[= output | eagerImpl table input] *
          expectedSimulatedQueryCount (eagerUnitImpl table) predicate (next output) () := by
  rw [expectedSimulatedQueryCount_query_bind]
  congr 1
  exact tsum_probOutput_map_mul _ _ _

theorem expectedDeferredProbeQueries_query_bind (state : AdaptiveRevealMonitor.State Index)
    (input : (World Index).Domain) (next : (World Index).Range input → OracleComp (World Index) α) :
    expectedDeferredProbeQueries state (liftM ((World Index).query input) >>= next) =
      (if IsProbeQuery input then 1 else 0) +
        ∑' base, Pr[= base | RevealProbeOracleSimulation.eagerTableSample] *
          ∑' output, Pr[= output | eagerImpl (RevealProbeOracleSimulation.extendTable state base) input] *
            expectedSimulatedQueryCount
              (eagerUnitImpl (RevealProbeOracleSimulation.extendTable state base))
              IsProbeQuery (next output) () := by
  unfold expectedDeferredProbeQueries
  simp_rw [expected_eagerUnit_query_bind, mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

theorem expectedDeferredProbeQueries_independent (state : AdaptiveRevealMonitor.State Index)
    (input : (World Index).Domain) (next : (World Index).Range input → OracleComp (World Index) α)
    (answers : ProbComp ((World Index).Range input))
    (hanswers : ∀ table : Index → Digest, eagerImpl table input = answers)
    (hprobe : ¬ IsProbeQuery input) :
    expectedDeferredProbeQueries state (liftM ((World Index).query input) >>= next) =
      ∑' output, Pr[= output | answers] * expectedDeferredProbeQueries state (next output) := by
  rw [expectedDeferredProbeQueries_query_bind]
  simp only [hprobe, if_false, zero_add, hanswers, expectedDeferredProbeQueries]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro output
  apply tsum_congr
  intro base
  exact mul_left_comm _ _ _

theorem expectedDeferredProbeQueries_probe (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (target : Digest) (next : Unit → OracleComp (World Index) α) :
    expectedDeferredProbeQueries state
        (liftM ((World Index).query (.probe index target)) >>= next) =
      1 + expectedDeferredProbeQueries state (next ()) := by
  rw [expectedDeferredProbeQueries_query_bind]
  simp only [IsProbeQuery, if_true, eagerImpl, tsum_probOutput_pure_mul]
  rfl

theorem expectedDeferredProbeQueries_addPending (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (target : Digest) (computation : OracleComp (World Index) α) :
    expectedDeferredProbeQueries (state.addPending index target) computation =
      expectedDeferredProbeQueries state computation := rfl

theorem expectedDeferredProbeQueries_reveal_known (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (value : Digest) (hknown : state.revealed index = some value)
    (next : Digest → OracleComp (World Index) α) :
    expectedDeferredProbeQueries state (liftM ((World Index).query (.reveal index)) >>= next) =
      expectedDeferredProbeQueries state (next value) := by
  rw [expectedDeferredProbeQueries_query_bind]
  simp only [IsProbeQuery, if_false, zero_add, eagerImpl, tsum_probOutput_pure_mul,
    RevealProbeOracleSimulation.extendTable, hknown, Option.getD_some]
  rfl

theorem expectedDeferredProbeQueries_reveal_fresh (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (hhidden : state.revealed index = none)
    (next : Digest → OracleComp (World Index) α) :
    expectedDeferredProbeQueries state (liftM ((World Index).query (.reveal index)) >>= next) =
      ∑' value, Pr[= value | $ᵗ Digest] *
        expectedDeferredProbeQueries (state.install index value) (next value) := by
  rw [expectedDeferredProbeQueries_query_bind]
  simp only [IsProbeQuery, if_false, zero_add, eagerImpl, tsum_probOutput_pure_mul]
  rw [expected_uniformTable_update index]
  apply tsum_congr
  intro value
  congr 1
  apply tsum_congr
  intro base
  rw [RevealProbeOracleSimulation.extendTable_update_eq_install state index value base hhidden]
  simp only [RevealProbeOracleSimulation.extendTable, AdaptiveRevealMonitor.State.install,
    Function.update_self, Option.getD_some]

noncomputable def chainPendingRisk (state : AdaptiveRevealMonitor.State Index) : ℝ≥0∞ :=
  (state.pendingCount : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹

theorem chainPendingRisk_addPending_le (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (target : Digest) :
    chainPendingRisk (state.addPending index target) ≤
      chainPendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold chainPendingRisk
  calc
    _ ≤ ((state.pendingCount + 1 : ℕ) : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
      gcongr
      exact state.pendingCount_addPending_le index target
    _ = _ := by simp [add_mul]

theorem chainPendingRisk_install_add (state : AdaptiveRevealMonitor.State Index)
    (index : Index) (value : Digest) :
    ((state.pending index).card : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ +
      chainPendingRisk (state.install index value) = chainPendingRisk state := by
  unfold chainPendingRisk
  rw [← add_mul, ← Nat.cast_add, Nat.add_comm, state.pendingCount_install_add]

omit [Fintype Index] [DecidableEq Index] in
theorem expected_affine (computation : ProbComp α) (constant rate : ℝ≥0∞)
    (weight : α → ℝ≥0∞) :
    (∑' value, Pr[= value | computation] * (constant + rate * weight value)) =
      constant + rate * ∑' value, Pr[= value | computation] * weight value := by
  simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) rate]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
    tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

omit [Fintype Index] [DecidableEq Index] in
theorem probEvent_bind_le_affine (computation : ProbComp α) (next : α → ProbComp Bool)
    (constant rate : ℝ≥0∞) (weight : α → ℝ≥0∞)
    (hnext : ∀ value, Pr[(· = true) | next value] ≤ constant + rate * weight value) :
    Pr[(· = true) | computation >>= next] ≤
      constant + rate * ∑' value, Pr[= value | computation] * weight value := by
  rw [probEvent_bind_eq_tsum, ← expected_affine]
  exact ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hnext value)

theorem applyRevealRequest_true_probability_le_expected
    (state : AdaptiveRevealMonitor.State Index) (index : Index)
    (resume : Digest → AdaptiveRevealMonitor.State Index → ProbComp Bool)
    (cost : Digest → ℝ≥0∞)
    (hresume : ∀ value,
      Pr[(· = true) | resume value (state.install index value)] ≤
        chainPendingRisk (state.install index value) +
          ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * cost value) :
    Pr[(· = true) | applyRevealRequest state index resume] ≤
      chainPendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        ∑' value, Pr[= value | $ᵗ Digest] * cost value := by
  classical
  let remaining := chainPendingRisk (state.install index 0)
  have hremaining (value : Digest) : chainPendingRisk (state.install index value) = remaining := rfl
  have hpointwise (value : Digest) :
      Pr[(· = true) | if value ∈ state.pending index then pure true
        else resume value (state.install index value)] ≤
      (if value ∈ state.pending index then 1 else 0) +
        (remaining + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * cost value) := by
    by_cases hhit : value ∈ state.pending index
    · simp only [hhit, if_true, probEvent_pure]
      exact le_add_right le_rfl
    · simpa only [hhit, if_false, zero_add, hremaining] using hresume value
  unfold applyRevealRequest
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' value, Pr[= value | $ᵗ Digest] *
        ((if value ∈ state.pending index then 1 else 0) +
          (remaining + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * cost value)) :=
      ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hpointwise value)
    _ = Pr[fun value => value ∈ state.pending index | $ᵗ Digest] +
        (remaining + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          ∑' value, Pr[= value | $ᵗ Digest] * cost value) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      · rw [probEvent_eq_tsum_ite]
        apply tsum_congr
        intro value
        split_ifs <;> simp
      · simpa only [mul_add] using expected_affine ($ᵗ Digest) remaining
          ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ cost
    _ ≤ ((state.pending index).card : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ +
        (remaining + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          ∑' value, Pr[= value | $ᵗ Digest] * cost value) :=
      add_le_add (RevealProbeOracleSimulation.uniformDigest_mem_finset_le _) le_rfl
    _ = _ := by rw [← add_assoc, chainPendingRisk_install_add]

theorem structuralExperiment_chain_probability_le_expected
    (state : AdaptiveRevealMonitor.State Index)
    (hvalid : RevealProbeOracleSimulation.StateValid state)
    (fuel : Nat) (computation : OracleComp (World Index) α) :
    Pr[(· = true) | structuralExperiment none state fuel computation] ≤
      chainPendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedDeferredProbeQueries state computation := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simpa [structuralExperiment, runStructural, chainPendingRisk,
        expectedDeferredProbeQueries, RevealProbeOracleSimulation.eagerTableSample] using
        RevealProbeOracleSimulation.eagerFinalize_true_probability_le state hvalid
  | query_bind input next ih =>
      have hindependent (answers : ProbComp ((World Index).Range input)) (nextFuel : Nat)
          (hdist : evalDist (structuralExperiment none state fuel
              (liftM ((World Index).query input) >>= next)) =
            evalDist (answers >>= fun output => structuralExperiment none state nextFuel (next output)))
          (hcount : expectedDeferredProbeQueries state (liftM ((World Index).query input) >>= next) =
            ∑' output, Pr[= output | answers] * expectedDeferredProbeQueries state (next output)) :
          Pr[(· = true) | structuralExperiment none state fuel
            (liftM ((World Index).query input) >>= next)] ≤
            chainPendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
              expectedDeferredProbeQueries state (liftM ((World Index).query input) >>= next) := by
        rw [hcount]
        refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
        exact probEvent_bind_le_affine answers
          (fun output => structuralExperiment none state nextFuel (next output))
          _ _ _ (fun output => ih output state hvalid nextFuel)
      cases input with
      | uniform n =>
          apply hindependent (liftM (unifSpec.query n)) fuel
          · rw [structuralExperiment_query_bind]
            simp only [runEagerQuery]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          · exact expectedDeferredProbeQueries_independent state _ next _ (fun _ => rfl)
              (by simp [IsProbeQuery])
      | encodingQuery leafIndex =>
          cases fuel with
          | zero =>
              rw [structuralExperiment_query_bind]
              simp only [runEagerQuery, bind_pure_comp]
              exact le_add_right
                (RevealProbeOracleSimulation.eagerFinalize_true_probability_le state hvalid)
          | succ remaining =>
              apply hindependent uniformHashOutput remaining
              · rw [structuralExperiment_query_bind]
                simp only [runEagerQuery, applyEncodingRequest]
                exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
              · exact expectedDeferredProbeQueries_independent state _ next _ (fun _ => rfl)
                  (by simp [IsProbeQuery])
      | encodingSignAttempt leafIndex =>
          apply hindependent uniformHashOutput fuel
          · rw [structuralExperiment_query_bind]
            simp only [runEagerQuery, applyEncodingRequest]
            exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
          · exact expectedDeferredProbeQueries_independent state _ next _ (fun _ => rfl)
              (by simp [IsProbeQuery])
      | probe index target =>
          cases fuel with
          | zero =>
              rw [structuralExperiment_query_bind]
              simp only [runEagerQuery, bind_pure_comp]
              exact le_add_right
                (RevealProbeOracleSimulation.eagerFinalize_true_probability_le state hvalid)
          | succ remaining =>
              rw [structuralExperiment_query_bind, expectedDeferredProbeQueries_probe]
              cases hrevealed : state.revealed index with
              | some value =>
                  simp only [runEagerQuery, hrevealed]
                  change Pr[(· = true) | structuralExperiment none state remaining (next ())] ≤ _
                  refine (ih () state hvalid remaining).trans ?_
                  gcongr
                  exact le_add_left le_rfl
              | none =>
                  simp only [runEagerQuery, hrevealed]
                  change Pr[(· = true) | structuralExperiment none
                    (state.addPending index target) remaining (next ())] ≤ _
                  refine (ih () (state.addPending index target)
                    (hvalid.addPending index target hrevealed) remaining).trans ?_
                  rw [expectedDeferredProbeQueries_addPending]
                  calc
                    _ ≤ (chainPendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) +
                        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
                          expectedDeferredProbeQueries state (next ()) :=
                      add_le_add (chainPendingRisk_addPending_le state index target) le_rfl
                    _ = _ := by rw [mul_add, mul_one, add_assoc]
      | reveal index =>
          cases hrevealed : state.revealed index with
          | some value =>
              rw [structuralExperiment_query_bind,
                expectedDeferredProbeQueries_reveal_known state index value hrevealed]
              simp only [runEagerQuery, hrevealed, RevealProbeOracleSimulation.extendTable,
                Option.getD_some]
              exact ih value state hvalid fuel
          | none =>
              let resume := fun value nextState =>
                structuralExperiment none nextState fuel (next value)
              have hdist : evalDist (structuralExperiment none state fuel
                    (liftM ((World Index).query (.reveal index)) >>= next)) =
                  evalDist (applyRevealRequest state index resume) := by
                rw [structuralExperiment_query_bind]
                simp only [runEagerQuery, hrevealed]
                simpa [resume, structuralExperiment] using
                  evalDist_eagerTableSample_applyRevealRequest state index hrevealed
                    fun table value nextState => runStructural table none nextState fuel (next value)
              rw [expectedDeferredProbeQueries_reveal_fresh state index hrevealed]
              refine (probEvent_congr' (fun _ _ => Iff.rfl) hdist).le.trans ?_
              exact applyRevealRequest_true_probability_le_expected state index resume
                (fun value => expectedDeferredProbeQueries (state.install index value) (next value))
                (fun value => ih value (state.install index value) (hvalid.install index value) fuel)

theorem chainFirstLane_probability_eq_structuralExperiment
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    Pr[fun result => RevealProbeOracleSimulation.runObserved result.1
        AdaptiveRevealMonitor.State.empty result.2.2.chainActions = true |
      eagerExperiment computation] =
    Pr[(· = true) | structuralExperiment none AdaptiveRevealMonitor.State.empty fuel computation] := by
  unfold eagerExperiment structuralExperiment
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  congr 1
  rw [bind_pure_comp, probEvent_map]
  change Pr[fun result => RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty result.2.chainActions = true |
    (simulateQ (eagerTraceImpl table) computation).run] =
      Pr[(· = true) | runStructural table none AdaptiveRevealMonitor.State.empty fuel computation]
  calc
    _ = Pr[(· = true) | (fun result => runObserved table none
        AdaptiveRevealMonitor.State.empty result.2) <$>
          (simulateQ (eagerTraceImpl table) computation).run] := by
      rw [probEvent_map]
      apply probEvent_congr' (fun result _ => ?_) rfl
      simp [runObserved_eq_projected]
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl)
      (evalDist_runObserved_eagerTrace_eq_runStructural table none
        AdaptiveRevealMonitor.State.empty fuel computation hbound)

/-- A probe costs at most one inverse digest-space factor even if the adversary probes
before the value is revealed and chooses its later queries adaptively. -/
theorem chainFirstLane_eager_probability_le_expected
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    Pr[fun result => RevealProbeOracleSimulation.runObserved result.1
        AdaptiveRevealMonitor.State.empty result.2.2.chainActions = true |
      eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedEagerQueryCount IsProbeQuery computation := by
  rw [chainFirstLane_probability_eq_structuralExperiment fuel computation hbound]
  have h := structuralExperiment_chain_probability_le_expected AdaptiveRevealMonitor.State.empty
    RevealProbeOracleSimulation.stateValid_empty fuel computation
  simp only [chainPendingRisk, AdaptiveRevealMonitor.State.pendingCount_empty,
    Nat.cast_zero, zero_mul, zero_add] at h
  exact h

theorem expectedEagerQueryCount_hazards (computation : OracleComp (World Index) α) :
    expectedEagerQueryCount IsHazardQuery computation =
      expectedEagerQueryCount IsEncodingQuery computation + expectedEagerQueryCount IsProbeQuery computation := by
  unfold expectedEagerQueryCount
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro table
  rw [← mul_add]
  congr 1
  have hor := expectedSimulatedQueryCount_or_of_disjoint (eagerUnitImpl table)
    IsEncodingQuery IsProbeQuery
    (fun input => by cases input <;> simp [IsEncodingQuery, IsProbeQuery]) computation ()
  rw [← hor]
  apply le_antisymm
  · apply expectedSimulatedQueryCount_mono
    intro input
    cases input <;> simp [IsHazardQuery, IsEncodingQuery, IsProbeQuery]
  · apply expectedSimulatedQueryCount_mono
    intro input
    cases input <;> simp [IsHazardQuery, IsEncodingQuery, IsProbeQuery]

/-- Both components of the existing first-lane event are charged to the expected number
of hazard queries, without charging the unused part of a worst-case query allowance. -/
theorem combinedHit_eager_probability_le_expected
    (fuel : Nat) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery fuel) :
    Pr[fun result => CombinedHit result.1 result.2.2 | eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedEagerQueryCount IsHazardQuery computation := by
  calc
    _ ≤ Pr[fun result => CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
          result.2.2.encodingActions = true | eagerExperiment computation] +
        Pr[fun result => RevealProbeOracleSimulation.runObserved result.1
          AdaptiveRevealMonitor.State.empty result.2.2.chainActions = true | eagerExperiment computation] :=
      probEvent_or_le _ _ _
    _ ≤ ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedEagerQueryCount IsEncodingQuery computation +
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedEagerQueryCount IsProbeQuery computation :=
      add_le_add (encodingFirstLane_eager_probability_le_expected computation)
        (chainFirstLane_eager_probability_le_expected fuel computation hbound)
    _ = _ := by rw [expectedEagerQueryCount_hazards, mul_add]

/-- info: 'XmssSecurity.FirstLaneOracleSimulation.chainFirstLane_eager_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainFirstLane_eager_probability_le_expected

/-- info: 'XmssSecurity.FirstLaneOracleSimulation.combinedHit_eager_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combinedHit_eager_probability_le_expected

end XmssSecurity.FirstLaneOracleSimulation

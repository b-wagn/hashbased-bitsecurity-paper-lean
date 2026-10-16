import XmssSecurity.Proof.FirstLaneChainExpected
import XmssSecurity.Proof.EncodingAcceptanceBudget

/-! Accepted encodings in a first-lane trace are charged to fresh encoding samples from
both direct queries and signing attempts. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def IsEncodingSample : (World Index).Domain → Prop
  | .encodingQuery _ => True
  | .encodingSignAttempt _ => True
  | _ => False

noncomputable instance : DecidablePred (IsEncodingSample (Index := Index)) := Classical.decPred _

noncomputable def acceptedEncodingAction : ObservedAction Index → Bool
  | .encoding (.query _ output) => decide (Checksum.ValidDigest (truncateHash output))
  | .encoding (.sign _ output) => decide (Checksum.ValidDigest (truncateHash output))
  | .chain _ => false

noncomputable def TraceHasAcceptedEncoding (trace : ActionTrace Index) : Prop :=
  trace.any acceptedEncodingAction = true

omit [Fintype Index] [DecidableEq Index] in
theorem traceHasAcceptedEncoding_append (left right : ActionTrace Index) :
    TraceHasAcceptedEncoding (left ++ right) ↔
      TraceHasAcceptedEncoding left ∨ TraceHasAcceptedEncoding right := by
  simp [TraceHasAcceptedEncoding, List.any_append, Bool.or_eq_true]

omit [Fintype Index] [DecidableEq Index] in
theorem traceFragment_encodingAcceptance (table : Index → Digest)
    (input : (World Index).Domain) :
    Pr[fun output => TraceHasAcceptedEncoding (traceFragment input output) | eagerImpl table input] ≤
      if IsEncodingSample input then Checksum.acceptanceProbability else 0 := by
  cases input with
  | encodingQuery leafIndex =>
      simpa only [TraceHasAcceptedEncoding, traceFragment, acceptedEncodingAction,
        List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq,
        eagerImpl, uniformHashOutput, IsEncodingSample, if_true] using
          Checksum.probEvent_validDigest_uniformHashOutput.le
  | encodingSignAttempt leafIndex =>
      simpa only [TraceHasAcceptedEncoding, traceFragment, acceptedEncodingAction,
        List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq,
        eagerImpl, uniformHashOutput, IsEncodingSample, if_true] using
          Checksum.probEvent_validDigest_uniformHashOutput.le
  | uniform n => simp [TraceHasAcceptedEncoding, traceFragment, IsEncodingSample]
  | probe index target =>
      simp [TraceHasAcceptedEncoding, traceFragment, acceptedEncodingAction, IsEncodingSample]
  | reveal index =>
      simp [TraceHasAcceptedEncoding, traceFragment, acceptedEncodingAction, IsEncodingSample]

omit [Fintype Index] [DecidableEq Index] in
theorem traceEncodingAcceptance_probability_le_expected (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    Pr[fun result => TraceHasAcceptedEncoding result.2 |
      (simulateQ (eagerTraceImpl table) computation).run] ≤
      Checksum.acceptanceProbability *
        expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample computation () := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value => simp [simulateQ_pure, TraceHasAcceptedEncoding]
  | query_bind input next ih =>
      rw [eagerTrace_query_bind_run, probEvent_bind_eq_tsum, expected_eagerUnit_query_bind]
      have hpointwise (output : (World Index).Range input) :
          Pr[fun result => TraceHasAcceptedEncoding result.2 | (do
            let tail ← (simulateQ (eagerTraceImpl table) (next output)).run
            pure (tail.1, traceFragment input output ++ tail.2))] ≤
          (if TraceHasAcceptedEncoding (traceFragment input output) then 1 else 0) +
            Checksum.acceptanceProbability *
              expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample (next output) () := by
        rw [bind_pure_comp, probEvent_map]
        by_cases hhead : TraceHasAcceptedEncoding (traceFragment input output)
        · rw [if_pos hhead]
          exact le_add_right probEvent_le_one
        · simp only [if_neg hhead, zero_add]
          have hevent : (fun result : α × ActionTrace Index =>
              TraceHasAcceptedEncoding (traceFragment input output ++ result.2)) =
              fun result => TraceHasAcceptedEncoding result.2 := by
            funext result
            exact propext (by simp only [traceHasAcceptedEncoding_append, hhead, false_or])
          change Pr[fun result => TraceHasAcceptedEncoding (traceFragment input output ++ result.2) |
            (simulateQ (eagerTraceImpl table) (next output)).run] ≤ _
          rw [hevent]
          exact ih output
      calc
        _ ≤ ∑' output, Pr[= output | eagerImpl table input] *
            ((if TraceHasAcceptedEncoding (traceFragment input output) then 1 else 0) +
              Checksum.acceptanceProbability *
                expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample (next output) ()) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (hpointwise output)
        _ = Pr[fun output => TraceHasAcceptedEncoding (traceFragment input output) | eagerImpl table input] +
            Checksum.acceptanceProbability *
              ∑' output, Pr[= output | eagerImpl table input] *
                expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample (next output) () := by
          simp_rw [mul_add, mul_left_comm (Pr[= _ | _]) Checksum.acceptanceProbability]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
          congr 1
          rw [probEvent_eq_tsum_ite]
          apply tsum_congr
          intro output
          split_ifs <;> simp
        _ ≤ (if IsEncodingSample input then Checksum.acceptanceProbability else 0) +
            Checksum.acceptanceProbability *
              ∑' output, Pr[= output | eagerImpl table input] *
                expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample (next output) () :=
          add_le_add (traceFragment_encodingAcceptance table input) le_rfl
        _ = _ := by split_ifs <;> simp [mul_add]

theorem traceEncodingAcceptance_eager_probability_le_expected
    (computation : OracleComp (World Index) α) :
    Pr[fun result => TraceHasAcceptedEncoding result.2.2 | eagerExperiment computation] ≤
      Checksum.acceptanceProbability * expectedEagerQueryCount IsEncodingSample computation := by
  simp only [eagerExperiment, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  calc
    _ ≤ ∑' table, Pr[= table | RevealProbeOracleSimulation.eagerTableSample] *
        (Checksum.acceptanceProbability *
          expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample computation ()) :=
      ENNReal.tsum_le_tsum fun table => mul_le_mul' le_rfl
        (traceEncodingAcceptance_probability_le_expected table computation)
    _ = _ := by
      simp_rw [mul_left_comm (Pr[= _ | _]) Checksum.acceptanceProbability]
      rw [ENNReal.tsum_mul_left]
      rfl

/-- info: 'XmssSecurity.FirstLaneOracleSimulation.traceEncodingAcceptance_eager_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms traceEncodingAcceptance_eager_probability_le_expected

end XmssSecurity.FirstLaneOracleSimulation

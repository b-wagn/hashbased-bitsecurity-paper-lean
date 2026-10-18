import XmssSecurity.Proof.TargetSum.EUFCMA.FreshAcceptancePrefix
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The terminal deciding probe is needed only for a fresh, accepted encoding.
Its expected cost is the probability of that event in the public experiment. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

def PublicFreshAccepted (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedChain.GlobalHighDirectTracedState) : Prop :=
  ¬ SigningTranscript.ContainsRequest result.2.attackerTrace.toSigningLog result.1 ∧
    (Deciding.forgedEncoding result.2.causalState.cache key.secretKey.parameter result.1).isSome

noncomputable instance (key : CappedChain.ProgrammedGlobalChainKeygenView) : DecidablePred (PublicFreshAccepted key) :=
  Classical.decPred _

def FreshPrefixFirstLaneEvent (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : Forgery × CappedChain.SourceExactTracedState) : Prop :=
  Deciding.PrefixFirstLaneEvent key result ∧ SourcePrefixFreshAccepted key result

noncomputable def publicFreshPrefixProbeExecution (fuel : ℕ) (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) :
    OracleComp CappedChain.GlobalFirstLaneWorld (Forgery × CappedChain.GlobalHighDirectTracedState) := do
  let result ← FirstLaneOracleSimulation.enforceHazardBound fuel (Deciding.publicPrefixExecution adversary key edgeHigh)
  if PublicFreshAccepted key result then
    let _ ← Deciding.publicDecidingProbe result.1.epoch
      (Deciding.signedEncoding result.2.causalState.cache key.secretKey.parameter
        result.2.attackerTrace.toSigningLog result.1.epoch)
      (Deciding.prefixProbeEncoding result.2.causalState.cache key.secretKey.parameter result.1)
      result.1.signature.chainValue
    pure result
  else pure result

noncomputable def appendFreshPrefixProbe (fuel : ℕ) (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex :=
  if PublicFreshAccepted key result.1 then
    Deciding.appendPrefixProbe base key (result.1, FirstLaneOracleSimulation.enforceHazardTrace fuel result.2)
  else (result.1, FirstLaneOracleSimulation.enforceHazardTrace fuel result.2)

theorem publicFreshPrefixProbeExecution_eager (fuel : ℕ) (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (base : CappedChain.GlobalChainValueIndex → Digest)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (publicFreshPrefixProbeExecution fuel adversary key edgeHigh)).run =
      appendFreshPrefixProbe fuel base key <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (Deciding.publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicFreshPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_enforceHazardBound]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  by_cases haccepted : PublicFreshAccepted key result.1
  · simp only [haccepted, if_true, simulateQ_bind, WriterT.run_bind', Deciding.publicDecidingProbe_eager,
      pure_bind, simulateQ_pure, WriterT.run_pure', map_pure]
    simp [appendFreshPrefixProbe, haccepted, Deciding.appendPrefixProbe, Deciding.prefixProbeResult, Prod.map]
    rfl
  · simp [haccepted, appendFreshPrefixProbe, simulateQ_pure, Prod.map]
    rfl

theorem hazardCount_appendFreshPrefixProbe (fuel : ℕ) (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (appendFreshPrefixProbe fuel base key result).2 =
      min fuel (FirstLaneOracleSimulation.hazardCount result.2) + if PublicFreshAccepted key result.1 then 1 else 0 := by
  unfold appendFreshPrefixProbe
  split <;> simp_all [Deciding.appendPrefixProbe, Deciding.prefixProbeResult, FirstLaneOracleSimulation.hazardCount_append,
    Deciding.decidingProbeResult_hazardCount, hazardCount_enforceHazardTrace]

theorem hazardCount_appendFreshPrefixProbe_le (fuel : ℕ) (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : (Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (appendFreshPrefixProbe fuel base key result).2 ≤ fuel + 1 := by
  rw [hazardCount_appendFreshPrefixProbe]
  split_ifs <;> omega

def CoupledPrefixFreshAccepted
    (result : Deciding.BaseHighKey × ((Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)) : Prop :=
  PublicFreshAccepted result.1.1.1 result.2.1

def CoupledFreshProbedHit (fuel : ℕ)
    (result : Deciding.BaseHighKey × ((Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)) : Prop :=
  FirstLaneOracleSimulation.CombinedHit result.1.1.2 (appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2).2

theorem coupledFreshPrefixProbe_eq_map (fuel : ℕ) (adversary : Adversary) :
    Deciding.coupledFirstLaneProgram (publicFreshPrefixProbeExecution fuel adversary) =
      (fun result => (result.1, appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2)) <$>
        Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary) := by
  unfold Deciding.coupledFirstLaneProgram
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro key
  rw [publicFreshPrefixProbeExecution_eager]
  simp only [bind_map_left]

theorem expectedCoupledHazards_freshProbe_eq (fuel : ℕ) (adversary : Adversary) :
    expectedCoupledHazards (fuel + 1) (publicFreshPrefixProbeExecution fuel adversary) =
      expectedCoupledHazards fuel (Deciding.publicPrefixExecution adversary) +
        Pr[CoupledPrefixFreshAccepted | Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary)] := by
  classical
  unfold expectedCoupledHazards
  rw [coupledFreshPrefixProbe_eq_map, tsum_probOutput_map_mul]
  have hweight (result : Deciding.BaseHighKey ×
      ((Forgery × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)) :
      ((min (fuel + 1) (FirstLaneOracleSimulation.hazardCount (appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2).2) : ℕ) : ℝ≥0∞) =
        ((min fuel (FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞) + if CoupledPrefixFreshAccepted result then 1 else 0 := by
    rw [min_eq_right (hazardCount_appendFreshPrefixProbe_le fuel _ _ _),
      hazardCount_appendFreshPrefixProbe, Nat.cast_add]
    by_cases haccepted : CoupledPrefixFreshAccepted result <;> simp_all [CoupledPrefixFreshAccepted]
  simp_rw [hweight, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  split_ifs <;> simp

theorem coupledFreshProbedHit_probability_le (adversary : Adversary) (D : ℕ) :
    Pr[CoupledFreshProbedHit D | Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary)] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[CoupledPrefixFreshAccepted | Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary)] := by
  have hhit : Pr[CoupledFreshProbedHit D | Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary)] =
      Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1.1.2 (FirstLaneOracleSimulation.enforceHazardTrace (D + 1) result.2.2) |
        Deciding.coupledFirstLaneProgram (publicFreshPrefixProbeExecution D adversary)] := by
    rw [coupledFreshPrefixProbe_eq_map, probEvent_map]
    apply probEvent_congr' (fun result _ => ?_) rfl
    simp only [Function.comp_def]
    rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le _ _ (hazardCount_appendFreshPrefixProbe_le D _ _ _)]
    rfl
  rw [hhit]
  apply (coupled_enforcedHit_probability_le_expected (D + 1) _).trans
  rw [expectedCoupledHazards_freshProbe_eq, mul_add]
  apply add_le_add _ le_rfl
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul' (le_refl (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
    (expectedCoupledHazards_le D (Deciding.publicPrefixExecution adversary))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.coupledFreshProbedHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupledFreshProbedHit_probability_le

end XmssSecurity.TargetSum.EUFCMA

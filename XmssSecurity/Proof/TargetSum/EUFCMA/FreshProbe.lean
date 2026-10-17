import XmssSecurity.Proof.TargetSum.EUFCMA.FreshAcceptancePrefix
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe

/-! The terminal deciding probe is needed only for a fresh, accepted encoding.
Its expected cost is the probability of that event in the public experiment. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

def PublicFreshAccepted (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × GlobalHighDirectTracedState) : Prop :=
  ¬ SigningTranscript.ContainsRequest result.2.attackerTrace.toSigningLog result.1 ∧
    (forgedEncoding result.2.causalState.cache key.secretKey.parameter result.1).isSome

noncomputable instance (key : ProgrammedGlobalChainKeygenView) : DecidablePred (PublicFreshAccepted key) :=
  Classical.decPred _

def FreshPrefixFirstLaneEvent (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) : Prop :=
  PrefixFirstLaneEvent key result ∧ SourcePrefixFreshAccepted key result

noncomputable def publicFreshPrefixProbeExecution (fuel : ℕ) (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalHighDirectTracedState) := do
  let result ← enforceHazardBound fuel (publicPrefixExecution adversary key edgeHigh)
  if PublicFreshAccepted key result then
    let _ ← publicDecidingProbe result.1.epoch
      (signedEncoding result.2.causalState.cache key.secretKey.parameter
        result.2.attackerTrace.toSigningLog result.1.epoch)
      (prefixProbeEncoding result.2.causalState.cache key.secretKey.parameter result.1)
      result.1.signature.chainValue
    pure result
  else pure result

noncomputable def appendFreshPrefixProbe (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex :=
  if PublicFreshAccepted key result.1 then
    appendPrefixProbe base key (result.1, enforceHazardTrace fuel result.2)
  else (result.1, enforceHazardTrace fuel result.2)

theorem publicFreshPrefixProbeExecution_eager (fuel : ℕ) (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (simulateQ (eagerTraceImpl base) (publicFreshPrefixProbeExecution fuel adversary key edgeHigh)).run =
      appendFreshPrefixProbe fuel base key <$>
        (simulateQ (eagerTraceImpl base) (publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicFreshPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  rw [simulate_eagerTrace_enforceHazardBound]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  by_cases haccepted : PublicFreshAccepted key result.1
  · simp only [haccepted, if_true, simulateQ_bind, WriterT.run_bind', publicDecidingProbe_eager,
      pure_bind, simulateQ_pure, WriterT.run_pure', map_pure]
    simp [appendFreshPrefixProbe, haccepted, appendPrefixProbe, prefixProbeResult, Prod.map]
    rfl
  · simp [haccepted, appendFreshPrefixProbe, simulateQ_pure, Prod.map]
    rfl

theorem hazardCount_appendFreshPrefixProbe (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendFreshPrefixProbe fuel base key result).2 =
      min fuel (hazardCount result.2) + if PublicFreshAccepted key result.1 then 1 else 0 := by
  unfold appendFreshPrefixProbe
  split <;> simp_all [appendPrefixProbe, prefixProbeResult, hazardCount_append,
    decidingProbeResult_hazardCount, hazardCount_enforceHazardTrace]

theorem hazardCount_appendFreshPrefixProbe_le (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendFreshPrefixProbe fuel base key result).2 ≤ fuel + 1 := by
  rw [hazardCount_appendFreshPrefixProbe]
  split_ifs <;> omega

def CoupledPrefixFreshAccepted
    (result : BaseHighKey × ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)) : Prop :=
  PublicFreshAccepted result.1.1.1 result.2.1

def CoupledFreshProbedHit (fuel : ℕ)
    (result : BaseHighKey × ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)) : Prop :=
  CombinedHit result.1.1.2 (appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2).2

theorem coupledFreshPrefixProbe_eq_map (fuel : ℕ) (adversary : XmssSecurity.TargetSum.Adversary) :
    coupledFirstLaneProgram (publicFreshPrefixProbeExecution fuel adversary) =
      (fun result => (result.1, appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2)) <$>
        coupledFirstLaneProgram (publicPrefixExecution adversary) := by
  unfold coupledFirstLaneProgram
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro key
  rw [publicFreshPrefixProbeExecution_eager]
  simp only [bind_map_left]

theorem expectedCoupledHazards_freshProbe_eq (fuel : ℕ) (adversary : XmssSecurity.TargetSum.Adversary) :
    expectedCoupledHazards (fuel + 1) (publicFreshPrefixProbeExecution fuel adversary) =
      expectedCoupledHazards fuel (publicPrefixExecution adversary) +
        Pr[CoupledPrefixFreshAccepted | coupledFirstLaneProgram (publicPrefixExecution adversary)] := by
  classical
  unfold expectedCoupledHazards
  rw [coupledFreshPrefixProbe_eq_map, tsum_probOutput_map_mul]
  have hweight (result : BaseHighKey ×
      ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)) :
      ((min (fuel + 1) (hazardCount (appendFreshPrefixProbe fuel result.1.1.2 result.1.1.1 result.2).2) : ℕ) : ℝ≥0∞) =
        ((min fuel (hazardCount result.2.2) : ℕ) : ℝ≥0∞) + if CoupledPrefixFreshAccepted result then 1 else 0 := by
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

theorem coupledFreshProbedHit_probability_le (adversary : XmssSecurity.TargetSum.Adversary) (D : ℕ) :
    Pr[CoupledFreshProbedHit D | coupledFirstLaneProgram (publicPrefixExecution adversary)] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[CoupledPrefixFreshAccepted | coupledFirstLaneProgram (publicPrefixExecution adversary)] := by
  have hhit : Pr[CoupledFreshProbedHit D | coupledFirstLaneProgram (publicPrefixExecution adversary)] =
      Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (D + 1) result.2.2) |
        coupledFirstLaneProgram (publicFreshPrefixProbeExecution D adversary)] := by
    rw [coupledFreshPrefixProbe_eq_map, probEvent_map]
    apply probEvent_congr' (fun result _ => ?_) rfl
    simp only [Function.comp_def]
    rw [enforceHazardTrace_eq_self_of_count_le _ _ (hazardCount_appendFreshPrefixProbe_le D _ _ _)]
    rfl
  rw [hhit]
  apply (coupled_enforcedHit_probability_le_expected (D + 1) _).trans
  rw [expectedCoupledHazards_freshProbe_eq, mul_add]
  apply add_le_add _ le_rfl
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul' (le_refl (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
    (expectedCoupledHazards_le D (publicPrefixExecution adversary))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.coupledFreshProbedHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupledFreshProbedHit_probability_le

end XmssSecurity.TargetSum.EUFCMA

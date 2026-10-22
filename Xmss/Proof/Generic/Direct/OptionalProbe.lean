import Xmss.Proof.Generic.Direct.ZeroHashPrefix
import Xmss.Proof.TargetSum.Direct.DecidingFirstLaneExpected

/-! A final probe is charged only on executions that actually make it. Fresh public randomness
can select its coordinate without revealing any additional chain values. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic.Deciding

variable [Code]

open CappedExecution FirstLaneOracleSimulation

abbrev ProbeChoice := Option (GlobalChainValueIndex × Digest)

def probeTrace : ProbeChoice → ActionTrace GlobalChainValueIndex
  | none => []
  | some (index, target) => [.chain (.probe index target)]

noncomputable def optionalProbe : ProbeChoice → OracleComp GlobalFirstLaneWorld Unit
  | none => pure ()
  | some (index, target) => probeQuery index target

theorem optionalProbe_eager (base : GlobalChainValueIndex → Digest) (choice : ProbeChoice) :
    (simulateQ (eagerTraceImpl base) (optionalProbe choice)).run =
      pure ((), probeTrace choice) := by
  cases choice with
  | none => simp [optionalProbe, probeTrace]
  | some choice =>
      rcases choice with ⟨index, target⟩
      simp [optionalProbe, probeTrace, probeQuery, eagerTraceImpl, eagerImpl, traceFragment,
        QueryImpl.withTraceAppend_apply]

noncomputable def sampledProbeExecution
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice)
    (key : ProgrammedGlobalChainKeygenView) : OracleComp GlobalFirstLaneWorld (α × Digest) := do
  let value ← body key
  let digest ← liftProbComp ($ᵗ Digest)
  optionalProbe (choose key value digest)
  pure (value, digest)

noncomputable def sampledPrefixProgram
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α) :
    ProbComp ((BaseKey × (α × ActionTrace GlobalChainValueIndex)) × Digest) := do
  let before ← coupledFirstLaneProgram body
  let digest ← $ᵗ Digest
  pure (before, digest)

def appendSampledProbe
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice)
    (sample : (BaseKey × (α × ActionTrace GlobalChainValueIndex)) × Digest) :
    BaseKey × ((α × Digest) × ActionTrace GlobalChainValueIndex) :=
  (sample.1.1, ((sample.1.2.1, sample.2),
    sample.1.2.2 ++ probeTrace (choose sample.1.1.1 sample.1.2.1 sample.2)))

theorem coupled_sampledProbe_eq
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice) :
    coupledFirstLaneProgram (sampledProbeExecution body choose) =
      appendSampledProbe choose <$> sampledPrefixProgram body := by
  unfold sampledPrefixProgram coupledFirstLaneProgram sampledProbeExecution appendSampledProbe
  simp only [simulateQ_bind, WriterT.run_bind', simulate_eagerTrace_liftProbComp,
    optionalProbe_eager, simulateQ_pure, WriterT.run_pure, bind_assoc, bind_map_left,
    pure_bind, Prod.map, List.nil_append, map_bind, map_pure]
  simp

theorem sampledPrefixProgram_support_prefix
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (sample : (BaseKey × (α × ActionTrace GlobalChainValueIndex)) × Digest)
    (hsample : sample ∈ support (sampledPrefixProgram body)) :
    sample.1 ∈ support (coupledFirstLaneProgram body) := by
  simp only [sampledPrefixProgram, mem_support_bind_iff, mem_support_pure_iff] at hsample
  obtain ⟨before, hbefore, digest, _, heq⟩ := hsample
  cases heq
  exact hbefore

theorem coupledFirstLaneProgram_support_body
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (before : BaseKey × (α × ActionTrace GlobalChainValueIndex))
    (hbefore : before ∈ support (coupledFirstLaneProgram body)) :
    before.2 ∈ support ((simulateQ (eagerTraceImpl before.1.2) (body before.1.1)).run) := by
  simp only [coupledFirstLaneProgram, mem_support_bind_iff, mem_support_pure_iff] at hbefore
  obtain ⟨key, _, result, hresult, heq⟩ := hbefore
  cases heq
  exact hresult

theorem sampledProbe_hazards_eq_probability
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice)
    (hzero : ∀ before ∈ support (coupledFirstLaneProgram body), hazardCount before.2.2 = 0) :
    TargetSum.Deciding.expectedCoupledHazards 1 (sampledProbeExecution body choose) =
      Pr[fun sample => (choose sample.1.1.1 sample.1.2.1 sample.2).isSome |
        sampledPrefixProgram body] := by
  classical
  unfold TargetSum.Deciding.expectedCoupledHazards
  rw [coupled_sampledProbe_eq, tsum_probOutput_map_mul, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro sample
  by_cases hsample : sample ∈ support (sampledPrefixProgram body)
  · have hprefix := sampledPrefixProgram_support_prefix body sample hsample
    simp only [appendSampledProbe, hazardCount_append, hzero _ hprefix, zero_add]
    cases hchoice : choose sample.1.1.1 sample.1.2.1 sample.2 <;>
      simp [probeTrace, hazardCount]
  · rw [probOutput_eq_zero_of_not_mem_support hsample]
    split_ifs <;> simp

theorem probeTrace_hidden_hit (base : GlobalChainValueIndex → Digest)
    (history : ActionTrace GlobalChainValueIndex) (index : GlobalChainValueIndex) (target : Digest)
    (hvalue : base index = target)
    (hhidden : ∀ value, ObservedAction.chain (.reveal index value) ∉ history) :
    CombinedHit base (history ++ probeTrace (some (index, target))) := by
  apply Or.inr
  refine globalRunObserved_eq_true_of_probe_mem_of_no_reveal base
    AdaptiveRevealMonitor.State.empty _ index target (by rfl) ?_ hvalue ?_
  · rw [chainAction_mem_iff]
    exact List.mem_append_right _ (by simp [probeTrace])
  · intro value hmem
    rw [chainAction_mem_iff, List.mem_append] at hmem
    rcases hmem with hpast | hprobe
    · exact hhidden value hpast
    · simp [probeTrace] at hprobe

def SampledProbeHit
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice)
    (sample : (BaseKey × (α × ActionTrace GlobalChainValueIndex)) × Digest) : Prop :=
  ∃ index target, choose sample.1.1.1 sample.1.2.1 sample.2 = some (index, target) ∧
    sample.1.1.2 index = target ∧
    ∀ value, ObservedAction.chain (.reveal index value) ∉ sample.1.2.2

theorem sampledProbe_hit_probability_le
    (body : ProgrammedGlobalChainKeygenView → OracleComp GlobalFirstLaneWorld α)
    (choose : ProgrammedGlobalChainKeygenView → α → Digest → ProbeChoice)
    (hzero : ∀ before ∈ support (coupledFirstLaneProgram body), hazardCount before.2.2 = 0) :
    Pr[SampledProbeHit choose | sampledPrefixProgram body] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[fun sample => (choose sample.1.1.1 sample.1.2.1 sample.2).isSome |
          sampledPrefixProgram body] := by
  classical
  calc
    _ ≤ Pr[fun result => CombinedHit result.1.2 (enforceHazardTrace 1 result.2.2) |
        coupledFirstLaneProgram (sampledProbeExecution body choose)] := by
      rw [coupled_sampledProbe_eq, probEvent_map]
      apply probEvent_mono
      intro sample hsample hhit
      obtain ⟨index, target, hchoice, hvalue, hhidden⟩ := hhit
      have hbefore := sampledPrefixProgram_support_prefix body sample hsample
      have hcount : hazardCount (appendSampledProbe choose sample).2.2 ≤ 1 := by
        simp [appendSampledProbe, hchoice, hazardCount_append, hzero _ hbefore,
          probeTrace, hazardCount]
      dsimp only [Function.comp_apply]
      rw [enforceHazardTrace_eq_self_of_count_le _ _ hcount]
      change CombinedHit sample.1.1.2
        (sample.1.2.2 ++ probeTrace (choose sample.1.1.1 sample.1.2.1 sample.2))
      rw [hchoice]
      exact probeTrace_hidden_hit _ _ index target hvalue hhidden
    _ ≤ _ := by
      simpa only [sampledProbe_hazards_eq_probability body choose hzero] using
        TargetSum.Deciding.coupled_enforcedHit_probability_le_expected 1
          (sampledProbeExecution body choose)

theorem zeroHash_public_prefix_hazards (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0)
    (before : CoupledPrefixResult)
    (hbefore : before ∈ support (coupledFirstLaneProgram (publicPrefixExecution adversary))) :
    hazardCount before.2.2 = 0 := by
  have hprob : Pr[fun result : CoupledPrefixResult => hazardCount result.2.2 ≠ 0 |
      coupledFirstLaneProgram (publicPrefixExecution adversary)] = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ Pr[fun _ : SourcePrefixResult => False | sourcePrefixProgram adversary] := by
        apply probEvent_le_of_relTriple (relTriple_symm (zeroHash_prefix_coupling adversary hzero))
        intro right left hrel hbad
        exact hbad hrel.hazards
      _ = 0 := by simp
  exact Classical.not_not.mp (probEvent_eq_zero_iff.mp hprob before hbefore)

noncomputable def sourceSampledPrefixProgram (adversary : Adversary) :
    ProbComp (SourcePrefixResult × Digest) := do
  let before ← sourcePrefixProgram adversary
  let digest ← $ᵗ Digest
  pure (before, digest)

theorem zeroHash_sampled_prefix_coupling (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    RelTriple (sourceSampledPrefixProgram adversary)
      (sampledPrefixProgram (publicPrefixExecution adversary))
      (fun left right => ZeroHashPrefixRelation left.1 right.1 ∧ left.2 = right.2) := by
  unfold sourceSampledPrefixProgram sampledPrefixProgram
  apply relTriple_bind (zeroHash_prefix_coupling adversary hzero)
  intro left right hrel
  apply relTriple_bind (relTriple_refl ($ᵗ Digest))
  intro ldigest rdigest heq
  apply relTriple_pure_pure
  exact ⟨hrel, heq⟩

theorem zeroHash_sampled_probe_probability_le (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0)
    (choose : ProgrammedGlobalChainKeygenView → (Forgery × GlobalDirectTracedState) →
      Digest → ProbeChoice)
    (event : SourcePrefixResult × Digest → Prop)
    (himp : ∀ left right,
      right ∈ support (sampledPrefixProgram (publicPrefixExecution adversary)) →
      ZeroHashPrefixRelation left.1 right.1 → left.2 = right.2 →
      event left → SampledProbeHit choose right) :
    Pr[event | sourceSampledPrefixProgram adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[fun sample => (choose sample.1.1.1 sample.1.2.1 sample.2).isSome |
          sampledPrefixProgram (publicPrefixExecution adversary)] := by
  calc
    _ ≤ Pr[SampledProbeHit choose | sampledPrefixProgram (publicPrefixExecution adversary)] := by
      apply probEvent_le_of_relTriple (relTriple_with_support
        (zeroHash_sampled_prefix_coupling adversary hzero))
      exact fun left right hrel => himp left right hrel.2.2 hrel.1.1 hrel.1.2
    _ ≤ _ := sampledProbe_hit_probability_le _ choose
      (zeroHash_public_prefix_hazards adversary hzero)

end Xmss.Generic.Deciding

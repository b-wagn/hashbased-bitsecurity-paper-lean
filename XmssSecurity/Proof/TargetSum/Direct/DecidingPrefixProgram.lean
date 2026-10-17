import XmssSecurity.Proof.TargetSum.Direct.DecidingPrefixEvent

/-! Programs for the first lane stopped before verification and followed by one deciding probe. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

abbrev BaseHighKey := (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
  (GlobalChainEdgeIndex → Digest)

noncomputable def coupledFirstLaneProgram
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    ProbComp (BaseHighKey × (α × ActionTrace GlobalChainValueIndex)) := do
  let key ← coupledGlobalChainKeygenWithBaseHighFull
  let result ← (simulateQ (eagerTraceImpl key.1.2) (body key.1.1 key.2)).run
  pure (key, result)

noncomputable def publicFirstLaneProgram
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    OracleComp GlobalFirstLaneWorld (GlobalHighDirectKeyResult × α) := do
  let key ← liftProbComp globalHighDirectKeygen
  let result ← body key.1 key.2
  pure (key, result)

def coupledFirstLaneProjection
    (result : BaseHighKey × (α × ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      ((GlobalHighDirectKeyResult × α) × ActionTrace GlobalChainValueIndex) :=
  (result.1.1.2, (((result.1.1.1, result.1.2), result.2.1), result.2.2))

theorem evalDist_coupledFirstLaneProgram_projection
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    evalDist (coupledFirstLaneProjection <$> coupledFirstLaneProgram body) =
      evalDist (eagerExperiment (publicFirstLaneProgram body)) := by
  let continuation := fun parameter base => do
    let key ← globalHighDirectKeygenAfterParameter parameter
    let result ← (simulateQ (eagerTraceImpl base) (body key.1 key.2)).run
    pure (base, ((key, result.1), result.2))
  have hproject : coupledFirstLaneProjection <$> coupledFirstLaneProgram body = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      continuation parameter base) := by
    unfold coupledFirstLaneProgram
    rw [coupledGlobalChainKeygenWithBaseHighFull_eq_direct]
    simp [coupledFirstLaneProjection, continuation, bind_assoc]
  have hafter (base : GlobalChainValueIndex → Digest) : (do
      let parameter ← Concrete.samplePublicParameter
      continuation parameter base) = (do
      let result ← (simulateQ (eagerTraceImpl base) (publicFirstLaneProgram body)).run
      pure (base, result)) := by
    unfold continuation publicFirstLaneProgram globalHighDirectKeygen
    simpa only [bind_assoc] using firstLane_eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Concrete.samplePublicParameter
        globalHighDirectKeygenAfterParameter parameter)
      (fun key => body key.1 key.2)
  rw [hproject]
  calc
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Concrete.samplePublicParameter
        continuation parameter base) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        Concrete.samplePublicParameter independentGlobalChainValueTable _
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let result ← (simulateQ (eagerTraceImpl base) (publicFirstLaneProgram body)).run
        pure (base, result)) := by
      rw [evalDist_bind, evalDist_bind]
      apply bind_congr
      intro base
      exact congrArg evalDist (hafter base)
    _ = _ := by
      unfold eagerExperiment
      rw [evalDist_bind, evalDist_bind]
      unfold independentGlobalChainValueTable RevealProbeOracleSimulation.eagerTableSample
      rfl

noncomputable def sourcePrefixExecution (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) : ProbComp (Forgery × SourceExactTracedState) :=
  (simulateQ (cappedBothTracedMappedAdversaryImpl key.publicKey
      (Concrete.materializePrecomputation key.cache key.secretKey))
    (adversary.main key.publicKey)).run ((((key.cache, []), []), []))

noncomputable def publicPrefixExecution (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalHighDirectTracedState) :=
  (simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh)
    (adversary.main key.publicKey)).run
      (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key))

noncomputable def sourcePrefixProgram (adversary : Adversary) :
    ProbComp (ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) := do
  let key ← trajectoryProgrammedGlobalChainKeygen
  let result ← sourcePrefixExecution adversary key
  pure (key, result)

noncomputable def publicPrefixProbeExecution (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalHighDirectTracedState) := do
  let result ← publicPrefixExecution adversary key edgeHigh
  let _ ← publicDecidingProbe result.1.epoch
    (signedEncoding result.2.causalState.cache key.secretKey.parameter
      result.2.attackerTrace.toSigningLog result.1.epoch)
    (prefixProbeEncoding result.2.causalState.cache key.secretKey.parameter result.1)
    result.1.signature.chainValue
  pure result

noncomputable def appendPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex :=
  (result.1, result.2 ++
    (prefixProbeResult base result.1.2.causalState.cache key.secretKey.parameter
      result.1.2.attackerTrace.toSigningLog result.1.1).2)

theorem publicPrefixProbeExecution_eager (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (simulateQ (eagerTraceImpl base) (publicPrefixProbeExecution adversary key edgeHigh)).run =
      appendPrefixProbe base key <$>
        (simulateQ (eagerTraceImpl base) (publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rw [publicDecidingProbe_eager]
  simp [appendPrefixProbe, prefixProbeResult, Prod.map]
  rfl

theorem prefixFirstLaneEvent_probability_le_enforcedHit_afterKeygen
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicPrefixProbeExecution adversary right.1.1 right.2)).run)
      (fun leftResult rightResult => PrefixFirstLaneEvent left leftResult →
        CombinedHit right.1.2 (enforceHazardTrace (D + 1) rightResult.2)) := by
  rw [publicPrefixProbeExecution_eager]
  have hpk : left.publicKey = right.1.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := relTriple_sourceExact_firstLane_adversary_boundedHit_direct D (D + 1)
    (by omega) adversary left right hkey hleftSupport hrightSupport (hD left.publicKey)
  have hrightProgram : (simulateQ (eagerTraceImpl right.1.2)
      (publicPrefixExecution adversary right.1.1 right.2)).run =
    (simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        (adversary.main left.publicKey)).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run := by
    unfold publicPrefixExecution
    rw [hpk]
  rw [hrightProgram]
  rw [← id_map (sourcePrefixExecution adversary left)]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro leftResult rightResult hresult hevent
  obtain ⟨hrel, _hleft, hright⟩ := hresult
  rcases hrel with ⟨hforgery, hgood, hcount⟩ | hhit
  · rw [hpk] at hright
    have hcovered := globalFirstLaneAdversary_support_returnedCovered right.1.1 right.1.2
      right.2 (adversary.main right.1.1.publicKey) rightResult hright
    have hhit := prefixFirstLaneEvent_good_implies_hit left right hkey hleftSupport hrightSupport
      leftResult rightResult hforgery hgood hcovered hevent
    rw [enforceHazardTrace_eq_self_of_count_le]
    · exact hhit
    · simpa only [appendPrefixProbe, prefixProbeResult, hazardCount_append,
        decidingProbeResult_hazardCount] using Nat.add_le_add_right hcount 1
  · exact CombinedHit.enforce_append_of_prefix _ _ _ _ hhit

end XmssSecurity.TargetSum.Deciding

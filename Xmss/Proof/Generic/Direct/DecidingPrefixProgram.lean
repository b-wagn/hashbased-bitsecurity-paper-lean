import Xmss.Proof.Generic.Direct.DecidingPrefixEvent

/-! Programs for the first lane stopped before verification and followed by one deciding probe. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic.Deciding

variable [Code]

open CappedExecution FirstLaneOracleSimulation

abbrev BaseKey := ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)

noncomputable def coupledFirstLaneProgram
    (body : ProgrammedGlobalChainKeygenView →
      OracleComp GlobalFirstLaneWorld α) :
    ProbComp (BaseKey × (α × ActionTrace GlobalChainValueIndex)) := do
  let key ← coupledGlobalChainKeygenWithBaseFull
  let result ← (simulateQ (eagerTraceImpl key.2) (body key.1)).run
  pure (key, result)

noncomputable def publicFirstLaneProgram
    (body : ProgrammedGlobalChainKeygenView →
      OracleComp GlobalFirstLaneWorld α) :
    OracleComp GlobalFirstLaneWorld (ProgrammedGlobalChainKeygenView × α) := do
  let key ← liftProbComp globalDirectKeygen
  let result ← body key
  pure (key, result)

def coupledFirstLaneProjection
    (result : BaseKey × (α × ActionTrace GlobalChainValueIndex)) :
    (GlobalChainValueIndex → Digest) ×
      ((ProgrammedGlobalChainKeygenView × α) × ActionTrace GlobalChainValueIndex) :=
  (result.1.2, ((result.1.1, result.2.1), result.2.2))

theorem evalDist_coupledFirstLaneProgram_projection
    (body : ProgrammedGlobalChainKeygenView →
      OracleComp GlobalFirstLaneWorld α) :
    evalDist (coupledFirstLaneProjection <$> coupledFirstLaneProgram body) =
      evalDist (eagerExperiment (publicFirstLaneProgram body)) := by
  let continuation := fun parameter base => do
    let key ← globalDirectKeygenAfterParameter parameter
    let result ← (simulateQ (eagerTraceImpl base) (body key)).run
    pure (base, ((key, result.1), result.2))
  have hproject : coupledFirstLaneProjection <$> coupledFirstLaneProgram body = (do
      let parameter ← Keygen.samplePublicParameter
      let base ← independentGlobalChainValueTable
      continuation parameter base) := by
    unfold coupledFirstLaneProgram
    rw [coupledGlobalChainKeygenWithBaseFull_eq_direct]
    simp [coupledFirstLaneProjection, continuation, bind_assoc]
  have hafter (base : GlobalChainValueIndex → Digest) : (do
      let parameter ← Keygen.samplePublicParameter
      continuation parameter base) = (do
      let result ← (simulateQ (eagerTraceImpl base) (publicFirstLaneProgram body)).run
      pure (base, result)) := by
    unfold continuation publicFirstLaneProgram globalDirectKeygen
    simpa only [bind_assoc] using firstLane_eagerTrace_liftProbComp_then_bind base
      (do
        let parameter ← Keygen.samplePublicParameter
        globalDirectKeygenAfterParameter parameter)
      body
  rw [hproject]
  calc
    _ = evalDist (do
        let base ← independentGlobalChainValueTable
        let parameter ← Keygen.samplePublicParameter
        continuation parameter base) :=
      OracleComp.DeferredSampling.evalDist_bind_comm
        Keygen.samplePublicParameter independentGlobalChainValueTable _
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
      (Keygen.materializePrecomputation key.cache key.secretKey))
    (adversary.main key.publicKey)).run ((((key.cache, []), []), []))

noncomputable def publicPrefixExecution (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalDirectTracedState) :=
  (simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl key)
    (adversary.main key.publicKey)).run
      (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState key))

noncomputable def sourcePrefixProgram (adversary : Adversary) :
    ProbComp (ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) := do
  let key ← trajectoryProgrammedGlobalChainKeygen
  let result ← sourcePrefixExecution adversary key
  pure (key, result)

noncomputable def publicPrefixProbeExecution (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalDirectTracedState) := do
  let result ← publicPrefixExecution adversary key
  let _ ← publicDecidingProbe result.1.epoch
    (signedEncoding result.2.causalState.cache key.secretKey.parameter
      result.2.attackerTrace.toSigningLog result.1.epoch)
    (prefixProbeEncoding result.2.causalState.cache key.secretKey.parameter result.1)
    result.1.signature.chainValue
  pure result

noncomputable def appendPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    (Forgery × GlobalDirectTracedState) × ActionTrace GlobalChainValueIndex :=
  (result.1, result.2 ++
    (prefixProbeResult base result.1.2.causalState.cache key.secretKey.parameter
      result.1.2.attackerTrace.toSigningLog result.1.1).2)

theorem publicPrefixProbeExecution_eager (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest) :
    (simulateQ (eagerTraceImpl base) (publicPrefixProbeExecution adversary key)).run =
      appendPrefixProbe base key <$>
        (simulateQ (eagerTraceImpl base) (publicPrefixExecution adversary key)).run := by
  unfold publicPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  apply bind_congr
  intro result
  rw [publicDecidingProbe_eager]
  simp [appendPrefixProbe, prefixProbeResult, Prod.map]
  rfl

theorem prefixFirstLaneEvent_probability_le_enforcedHit_afterKeygen
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseKey)
    (hkey : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.2)
        (publicPrefixProbeExecution adversary right.1)).run)
      (fun leftResult rightResult => PrefixFirstLaneEvent left leftResult →
        CombinedHit right.2 (enforceHazardTrace (D + 1) rightResult.2)) := by
  rw [publicPrefixProbeExecution_eager]
  have hpk : left.publicKey = right.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := relTriple_sourceExact_firstLane_adversary_boundedHit_direct D (D + 1)
    (by omega) adversary left right hkey hleftSupport hrightSupport (hD left.publicKey)
  have hrightProgram : (simulateQ (eagerTraceImpl right.2)
      (publicPrefixExecution adversary right.1)).run =
    (simulateQ (eagerTraceImpl right.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1)
        (adversary.main left.publicKey)).run
          (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState right.1)))).run := by
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
    have hcovered := globalFirstLaneAdversary_support_returnedCovered right.1 right.2
      (adversary.main right.1.publicKey) rightResult hright
    have hhit := prefixFirstLaneEvent_good_implies_hit left right hkey hleftSupport hrightSupport
      leftResult rightResult hforgery hgood hcovered hevent
    rw [enforceHazardTrace_eq_self_of_count_le]
    · exact hhit
    · simpa only [appendPrefixProbe, prefixProbeResult, hazardCount_append,
        decidingProbeResult_hazardCount] using Nat.add_le_add_right hcount 1
  · exact CombinedHit.enforce_append_of_prefix _ _ _ _ hhit

end Xmss.Generic.Deciding

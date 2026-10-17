import XmssSecurity.Proof.TargetSum.CappedExactFirstLaneBound
import XmssSecurity.Proof.TargetSum.Direct.Basic

/-!
# The first lane under a direct query bound

A version of `CappedExactFirstLaneBound` in which the adversary is charged only for its own
(direct) hash queries, bounded syntactically by `Direct.IsDirectQueryBound adversary D`, while the
final verification is charged `Direct.verifierQueryBound` hash calls.
-/

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.TargetSum.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem relTriple_sourceExact_firstLane_detailedExecution_boundedHit_direct
    (D countLimit hitLimit : Nat)
    (hcountLimit : countLimit = D + Direct.verifierQueryBound)
    (adversary : Adversary)
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (hD' : (adversary.main left.publicKey).IsQueryBoundP Direct.IsDirectHashQuery D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      (sourceGlobalExactTracedDetailedExecution adversary left)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
        ((globalFirstLaneExactTracedDetailedExecution adversary right.1.1
          right.2).run (GlobalHighDirectTracedState.initial
            (globalFilteredCausalKeygenState right.1.1)))).run)
      (fun leftResult firstLaneResult =>
        ((leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
            firstLaneResult.1.2 firstLaneResult.2 ∧
          FirstLaneOracleSimulation.hazardCount firstLaneResult.2 ≤
            countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit right.1.2
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            firstLaneResult.2))) := by
  let secretKey :=
    Concrete.materializePrecomputation left.cache left.secretKey
  let sourceInitial : SourceExactTracedState := ((((left.cache, []), []), []))
  let highInitial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState right.1.1, []⟩, [])
  let firstLaneInitial : GlobalHighDirectTracedState :=
    GlobalHighDirectTracedState.initial
      (globalFilteredCausalKeygenState right.1.1)
  have hinitial : SourceFirstLaneExactGoodStateRelation left right.1
      sourceInitial firstLaneInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, highInitial, firstLaneInitial,
        globalStateOfFirstLane, sourceExactSigningProjection,
        FirstLaneOracleSimulation.ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel
          hleftSupport hrightSupport
    · simp [sourceInitial,
        FirstLaneOracleSimulation.ActionTrace.encodingActions]
    · simp [CappedEncodingMonitor.validObservedSignLeafIndices,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
  let Budget := fun
    (rest : OracleComp (OracleWorld + SigningSpec) Forgery)
    (remaining : Nat) (_state : SourceExactTracedState) =>
      Direct.verifierQueryBound ≤ remaining ∧
        rest.IsQueryBoundP Direct.IsDirectHashQuery
          (remaining - Direct.verifierQueryBound)
  let leftFinish := fun (forgery : Forgery)
    (initial : SourceExactTracedState) => do
      let verified ← (simulateQ sourceSigningTracedVerifierImpl
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run (sourceExactSigningProjection initial)
      pure ((forgery, verified.1),
        ((verified.2.1,
          appendVerificationEncodingObservation secretKey forgery
            initial.1.1.1 verified.2.1.1 initial.1.2), verified.2.2))
  let rightFinish := fun (forgery : Forgery)
    (initial : GlobalHighDirectTracedState) => do
      let verified ← (simulateQ
        (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
        (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
          forgery.signature)).run initial
      pure ((forgery, verified.1),
        firstLaneAppendVerificationState right.1.1.secretKey forgery initial
          verified.2)
  have hfullBound : Budget (adversary.main left.publicKey) countLimit sourceInitial := by
    refine ⟨by omega, ?_⟩
    rw [hcountLimit, Nat.add_sub_cancel]
    exact hD'
  have hcoupling := relTriple_simulateQ_bind_bounded_firstLane right.1.2
    (cappedBothTracedMappedAdversaryImpl left.publicKey secretKey)
    (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
    leftFinish rightFinish directHashActionCost
    (SourceFirstLaneExactGoodStateRelation left right.1)
    (fun state spent => state.2.hashInputs.length = spent) Budget
    (by
      intro input next remaining state result hrest _hresult
      unfold Budget at hrest ⊢
      obtain ⟨hle, hq⟩ := hrest
      rw [isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hpos, hnext⟩ := hq
      have hn := hnext result.1
      rw [Direct.directHashActionCost_eq_if]
      by_cases hdirect : Direct.IsDirectHashQuery input
      · have hpos' : 0 < remaining - Direct.verifierQueryBound :=
          hpos.resolve_left (not_not.mpr hdirect)
        rw [if_pos hdirect] at hn ⊢
        refine ⟨by omega, by omega, ?_⟩
        have heq : remaining - 1 - Direct.verifierQueryBound =
            remaining - Direct.verifierQueryBound - 1 := by omega
        rw [heq]
        exact hn
      · rw [if_neg hdirect] at hn ⊢
        exact ⟨Nat.zero_le _, by simpa using hle, by simpa using hn⟩)
    (by
      intro spent input state firstState history hstates hprefix hacct
      apply relTriple_post_mono
        (relTriple_sourceExact_firstLane_action spent left right hrel
          hleftSupport hrightSupport input state firstState history hstates
            hprefix)
      intro leftResult firstResult hresult
      rcases hresult with hgood | hhit
      · exact Or.inl ⟨hgood.1, hgood.2.1, hgood.2.2.1, by
          rw [hgood.2.2.2, hacct]⟩
      · exact Or.inr hhit)
    countLimit hitLimit
    (by
      intro forgery spent remaining state firstState history hremaining
        hstates hcount hacct htotal
      unfold Budget at hremaining
      have hverifyBound :
          HashQueryBound (Concrete.scheme.verify left.publicKey forgery.epoch forgery.message
            forgery.signature) state.1.1.1 remaining := by
        intro verifyResult hverifyResult
        exact le_trans
          (hverify left.publicKey forgery.epoch forgery.message forgery.signature
            state.1.1.1 verifyResult hverifyResult) hremaining.1
      have hverifier :=
        relTriple_sourceExact_firstLane_verifier_boundedHit countLimit hitLimit
          spent remaining left right hrel hleftSupport hrightSupport
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature) state hverifyBound firstState
                history hstates hcount htotal hlimits
      let sourceFinish := fun verified : Bool × SourceExactTracedState =>
        ((forgery, verified.1),
          sourceAppendVerificationState secretKey forgery state verified.2)
      let firstFinish := fun verified :
          ((Bool × GlobalHighDirectTracedState) ×
            FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (((forgery, verified.1.1),
          firstLaneAppendVerificationState right.1.1.secretKey forgery
            firstState verified.1.2), verified.2)
      have hlifted : RelTriple
          (sourceFinish <$>
            (simulateQ sourceExactTracedVerifierImpl
              (Concrete.scheme.verify left.publicKey forgery.epoch
                forgery.message forgery.signature)).run state)
          (firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run)
          (fun leftResult firstResult =>
            (leftResult.1 = firstResult.1.1 ∧
              SourceFirstLaneExactGoodStateRelation left right.1 leftResult.2
                firstResult.1.2 (history ++ firstResult.2) ∧
              FirstLaneOracleSimulation.hazardCount
                (history ++ firstResult.2) ≤ countLimit) ∨
            FirstLaneOracleSimulation.CombinedHit right.1.2
              (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                (history ++ firstResult.2))) := by
        apply relTriple_map
        apply relTriple_post_mono (relTriple_with_support hverifier)
        intro leftVerified firstVerified hvertified
        obtain ⟨hverifiedRelation, hleftVerifiedSupport,
          hfirstVerifiedSupport⟩ := hvertified
        rcases hverifiedRelation with hgood | hhit
        · exact Or.inl ⟨congrArg (Prod.mk forgery) hgood.1,
            SourceFirstLaneExactGoodStateRelation.appendVerification left right
              hrel hleftSupport hrightSupport forgery state leftVerified.2
                firstState firstVerified.1.2 history
                  (history ++ firstVerified.2) hstates hgood.2.1 (by
                    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
                    have hpublicKey : left.publicKey =
                        right.1.1.publicKey := hrel.1.toStable.1.2.1
                    rw [hpublicKey] at hfirstVerifiedSupport
                    have hlocal :=
                      globalFirstLaneExactTracedVerifier_append_trace_sublist
                        right.1.2 right.1.1 right.2 forgery firstState
                          leftVerified.2.1.2
                          (by
                            have hkeyResult :=
                              trajectoryProgrammedGlobalChainKeygen_support_keyResult
                                right.1.1 hrightSupport
                            exact keygen_parameter_eq right.1.1.keyResult
                              hkeyResult)
                          firstVerified hfirstVerifiedSupport
                    have hleftEncoding : leftVerified.2.1.2 = state.1.2 := by
                      rw [sourceExactTracedVerifierImpl_run_eq, support_map]
                        at hleftVerifiedSupport
                      obtain ⟨baseResult, _hbase, heq⟩ := hleftVerifiedSupport
                      subst leftVerified
                      rfl
                    have hencodingInitial := hstates.2.1
                    have hencodingFinal : List.Sublist leftVerified.2.1.2
                        history.encodingActions := by
                      rw [hleftEncoding]
                      exact hencodingInitial
                    exact hlocal.trans
                      (hencodingFinal.append (List.Sublist.refl _))),
            hgood.2.2⟩
        · exact Or.inr hhit
      have hsource : leftFinish forgery state = sourceFinish <$>
          (simulateQ sourceExactTracedVerifierImpl
            (Concrete.scheme.verify left.publicKey forgery.epoch
              forgery.message forgery.signature)).run state := by
        unfold leftFinish
        rw [sourceExactTracedVerifierImpl_run_eq]
        simp [sourceFinish, sourceAppendVerificationState, Functor.map_map]
      have hright :
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
            (rightFinish forgery firstState)).run =
          firstFinish <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((simulateQ
                (globalFirstLaneExactTracedVerifierImpl right.1.1 right.2)
                (Concrete.scheme.verify left.publicKey forgery.epoch
                  forgery.message forgery.signature)).run firstState)).run := by
        unfold rightFinish
        rw [simulateQ_bind, WriterT.run_bind']
        simp [firstFinish, firstLaneAppendVerificationState]
      rw [hsource, hright]
      exact hlifted)
    0 countLimit (adversary.main left.publicKey) sourceInitial
      firstLaneInitial hfullBound [] hinitial
      (by simp [FirstLaneOracleSimulation.hazardCount]) (by rfl) (by omega)
        hlimits
  have hpublicKey : left.publicKey = right.1.1.publicKey :=
    hrel.1.toStable.1.2.1
  unfold sourceGlobalExactTracedDetailedExecution
    globalFirstLaneExactTracedDetailedExecution
  simp only [StateT.run_mk]
  rw [← hpublicKey]
  exact hcoupling

theorem relTriple_sourceGlobalExact_firstLane_program_boundedHit_direct
    (D hitLimit : Nat)
    (adversary : Adversary)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound)
    (hlimits : D + Direct.verifierQueryBound ≤ hitLimit) :
    RelTriple (sourceGlobalExactTracedProgram adversary)
      (globalFirstLaneExactCoupledProgram adversary)
      (SourceFirstLaneExactBoundedProgramRelation
        (D + Direct.verifierQueryBound) hitLimit) := by
  unfold sourceGlobalExactTracedProgram globalFirstLaneExactCoupledProgram
  apply relTriple_bind
    (relTriple_with_support
      relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeygen
  obtain ⟨hrel, hleftSupport, hrightSupport⟩ := hkeygen
  have hrightViewSupport :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  apply relTriple_bind
    (relTriple_sourceExact_firstLane_detailedExecution_boundedHit_direct
      D (D + Direct.verifierQueryBound) hitLimit rfl adversary left right hrel
        hleftSupport hrightViewSupport (hD left.publicKey) hverify hlimits)
  intro leftExecution rightExecution hexecution
  apply relTriple_pure_pure
  exact ⟨hrel, hexecution⟩

theorem sourceWinningExactFirstLane_probability_le_coupled_enforcedHit_direct
    (D fuel : Nat)
    (adversary : Adversary)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound)
    (hfuel : D + Direct.verifierQueryBound + numChains ≤ fuel) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] := by
  apply probEvent_le_of_relTriple
    (relTriple_with_support
      (relTriple_sourceGlobalExact_firstLane_program_boundedHit_direct
        D fuel adversary hD hverify (by omega)))
  intro left right hrelation hevent
  exact sourceWinningExactFirstLane_implies_coupled_enforcedHit
    (D + Direct.verifierQueryBound) fuel adversary left right
      hrelation.2.1 hrelation.2.2 hrelation.1 hfuel hevent

theorem sourceWinningExactFirstLane_probability_le_direct
    (D : Nat)
    (adversary : Adversary)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound) :
    Pr[SourceWinningExactFirstLaneEvent |
        sourceGlobalExactTracedProgram adversary] ≤
      ((D + Direct.verifierQueryBound + numChains : Nat) : ENNReal) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  let fuel := D + Direct.verifierQueryBound + numChains
  calc
    _ ≤ Pr[GlobalFirstLaneExactCoupledEnforcedHit fuel |
        globalFirstLaneExactCoupledProgram adversary] :=
      sourceWinningExactFirstLane_probability_le_coupled_enforcedHit_direct D fuel
        adversary hD hverify (by simp [fuel])
    _ = Pr[GlobalFirstLaneExactPublicEnforcedHit fuel |
        globalFirstLaneExactPublicEagerExperiment adversary] :=
      coupled_enforcedHit_probability_eq_public_eager fuel adversary
    _ ≤ _ := public_eager_enforcedHit_probability_le fuel adversary

theorem hasExactFirstLaneBound_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hverify : ∀ (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
      (signature : Signature) (cache : QueryCache HashSpec),
      HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
        Direct.verifierQueryBound) :
    Pr[WinningExactFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((D + Direct.verifierQueryBound + numChains : ℕ) : ℝ≥0∞) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [cappedExactFirstLane_probability_eq_sourceGlobalExact]
  exact sourceWinningExactFirstLane_probability_le_direct D adversary hD hverify

end XmssSecurity.TargetSum.CappedChain

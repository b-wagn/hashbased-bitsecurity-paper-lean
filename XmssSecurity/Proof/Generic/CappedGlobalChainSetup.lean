import XmssSecurity.Proof.Generic.CappedGlobalCausalSetup
import XmssSecurity.Proof.Common.MarginalCoupling
import XmssSecurity.Proof.Generic.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Generic.CappedChain

variable [Code]

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem relTriple_programmedGlobalChainTrajectoryMaterial_withBase
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBase parameter)
      (fun left right => globalChainTrajectoryMaterialTable left = right.2) := by
  classical
  exact relTriple_of_evalDist_map_eq_general
    (programmedGlobalChainTrajectoryMaterial parameter)
    (programmedGlobalChainTrajectoryMaterialWithBase parameter)
    globalChainTrajectoryMaterialTable globalChainTrajectoryMaterialBase
    (evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base parameter)

noncomputable def coupledGlobalChainKeygenWithBase
    (parameter : PublicParameter) :
    ProbComp (CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) := do
  let materialBase ←
    programmedGlobalChainTrajectoryMaterialWithBase parameter
  let material := materialBase.1
  let tree ← treeValues parameter material.1 allTreeValueIndices material.2.2
  pure (({
    secret := material.1
    table := globalChainTrajectoryMaterialTable material
    values := tree.1
    cache := tree.2
  } : CoupledGlobalChainKeygenView), materialBase.2)

def CoupledGlobalChainKeygenBaseRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenFullCacheRelation parameter left right ∧
    GlobalChainTableEdgesMatch left.cache parameter left.table

theorem programmedGlobalChainTrajectoryMaterialWithBase_support_material
    (parameter : PublicParameter)
    (materialBase : GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest))
    (hmaterialBase : materialBase ∈ support
      (programmedGlobalChainTrajectoryMaterialWithBase parameter)) :
    materialBase.1 ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter) := by
  unfold programmedGlobalChainTrajectoryMaterialWithBase at hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBase
  obtain ⟨base, _hbase, hmaterialBind⟩ := hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBind
  obtain ⟨material, hmaterial, hpure⟩ := hmaterialBind
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  exact hmaterial

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygen_withBase
    (parameter : PublicParameter) :
    RelTriple
      (coupledGlobalChainKeygenExperiment parameter)
      (coupledGlobalChainKeygenWithBase parameter)
      (CoupledGlobalChainKeygenBaseRelation parameter) := by
  unfold coupledGlobalChainKeygenExperiment
    coupledGlobalChainKeygenWithBase
  apply relTriple_bind (relTriple_with_support
    (relTriple_programmedGlobalChainTrajectoryMaterial_withBase parameter))
  intro leftMaterial rightMaterialBase hmaterial
  rcases hmaterial with ⟨htable, hleftSupport, hrightSupport⟩
  have hrightMaterialSupport :=
    programmedGlobalChainTrajectoryMaterialWithBase_support_material parameter
      rightMaterialBase hrightSupport
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_globalMaterial_allTreeValues_run parameter leftMaterial
        rightMaterialBase.1 hleftSupport hrightMaterialSupport))
  intro leftTree rightTree htree
  obtain ⟨htreeRelation, hleftTreeSupport, hrightTreeSupport⟩ := htree
  obtain ⟨hvalues, leftEndpoints, rightEndpoints, hcache,
    hleftEndpoints, hrightEndpoints⟩ := htreeRelation
  have hleftReplay := treeValues_support_replay parameter leftMaterial.1
    allTreeValueIndices leftMaterial.2.2 leftTree hleftTreeSupport
  have hrightReplay := treeValues_support_replay parameter
    rightMaterialBase.1.1 allTreeValueIndices
      rightMaterialBase.1.2.2 rightTree hrightTreeSupport
  have hmatches := programmedGlobalChainTrajectoryMaterial_edgesMatch
    parameter leftMaterial hleftSupport
  have hcacheLe := treeValues_cache_le parameter leftMaterial.1
    allTreeValueIndices leftMaterial.2.2 leftTree hleftTreeSupport
  apply relTriple_pure_pure
  refine ⟨?_, ?_⟩
  · unfold CoupledGlobalChainKeygenFullCacheRelation
      CoupledGlobalChainKeygenRelation
    refine ⟨⟨htable, ?_, ?_, hvalues, hleftReplay, hrightReplay⟩,
      leftEndpoints, rightEndpoints, hcache, hleftEndpoints,
        hrightEndpoints⟩
    · exact globalTreeValuesReplay_eq_root parameter leftMaterial.1
        rightMaterialBase.1.1 leftTree.2 rightTree.2 leftTree.1
          hleftReplay (hvalues ▸ hrightReplay)
    · intro leafIndex
      exact globalTreeValuesReplay_eq_authenticationPath parameter
        leftMaterial.1 rightMaterialBase.1.1 leftTree.2 rightTree.2
          leftTree.1 hleftReplay (hvalues ▸ hrightReplay) leafIndex
  · exact hmatches.mono hcacheLe


set_option maxRecDepth 2000000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable def coupledGlobalChainKeygenWithBaseFull :
    ProbComp (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledGlobalChainKeygenWithBase parameter
  pure (result.1.toProgrammedView parameter, result.2)

def ProgrammedGlobalChainKeygenBaseFullRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygenWithBaseFull :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseFull
      ProgrammedGlobalChainKeygenBaseFullRelation := by
  unfold coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseFull
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledGlobalChainKeygen_withBase leftParameter)
  intro leftView rightView hview
  apply relTriple_pure_pure
  refine ⟨?_, ?_⟩
  · unfold ProgrammedGlobalChainKeygenFullCacheRelation
      ProgrammedGlobalChainKeygenFullRelation
      ProgrammedGlobalChainKeygenRelation
      CoupledGlobalChainKeygenView.toProgrammedView
    refine ⟨⟨⟨hview.1.1.1, ?_, hview.1.1.2.2.1⟩, leftView.values,
      hview.1.1.2.2.2.2.1, ?_⟩, hview.1.2⟩
    · exact congrArg (fun root => PublicKey.mk root leftParameter)
        hview.1.1.2.1
    · rw [hview.1.1.2.2.2.1]
      exact hview.1.1.2.2.2.2.2
  · exact hview.2

theorem coupledGlobalChainKeygenWithBaseFull_support_keyView
    (result : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hresult : result ∈ support
      coupledGlobalChainKeygenWithBaseFull) :
    result.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold coupledGlobalChainKeygenWithBaseFull at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hparameterBind⟩ := hresult
  rw [mem_support_bind_iff] at hparameterBind
  obtain ⟨viewBase, hviewBase, hpureView⟩ := hparameterBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureView
  unfold coupledGlobalChainKeygenWithBase at hviewBase
  rw [mem_support_bind_iff] at hviewBase
  obtain ⟨materialBase, hmaterialBase, htreeBind⟩ := hviewBase
  rw [mem_support_bind_iff] at htreeBind
  obtain ⟨tree, htree, hpureTree⟩ := htreeBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureTree
  have hmaterial :=
    programmedGlobalChainTrajectoryMaterialWithBase_support_material parameter
      materialBase hmaterialBase
  let expectedCoupled : CoupledGlobalChainKeygenView := {
    secret := materialBase.1.1
    table := globalChainTrajectoryMaterialTable materialBase.1
    values := tree.1
    cache := tree.2
  }
  have hparameterView : expectedCoupled ∈ support
      (coupledGlobalChainKeygenExperiment parameter) := by
    unfold coupledGlobalChainKeygenExperiment
    rw [mem_support_bind_iff]
    refine ⟨materialBase.1, hmaterial, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨tree, htree, by simp [expectedCoupled]⟩
  have hcoupled : expectedCoupled.toProgrammedView parameter ∈
      support coupledGlobalChainKeygen := by
    unfold coupledGlobalChainKeygen
    rw [mem_support_bind_iff]
    refine ⟨parameter, hparameter, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨expectedCoupled, hparameterView, by simp⟩
  have hkeyView : result.1 = expectedCoupled.toProgrammedView parameter := by
    rw [hpureView, hpureTree]
  rw [hkeyView]
  exact (mem_support_iff_of_evalDist_eq
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed _).mp hcoupled

def ProgrammedGlobalChainKeygenBaseStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheStableRelation left right ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygen_withBase_fullCacheStable :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseFull
      ProgrammedGlobalChainKeygenBaseStableRelation := by
  apply relTriple_post_mono
    (relTriple_with_support
      relTriple_coupledGlobalChainKeygenWithBaseFull)
  intro left right hrel
  obtain ⟨hbase, hleftCoupledSupport, hrightSupport⟩ := hrel
  have hleftSupport : left ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    (mem_support_iff_of_evalDist_eq
      evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed left).mp
        hleftCoupledSupport
  have hrightViewSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    coupledGlobalChainKeygenWithBaseFull_support_keyView right
      hrightSupport
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightViewSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hbase.1.1.1.2.1
      _ = right.1.secretKey.parameter :=
        keygen_parameter_eq right.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, hcache, hleftReplay,
    hrightReplay⟩ := hbase.1.2
  refine ⟨?_, hbase.2⟩
  refine ⟨hbase.1,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable left
      hleftSupport,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable right.1
      hrightViewSupport,
    leftEndpoints, rightEndpoints, hcache, hleftReplay, ?_⟩
  rw [hparameter]
  exact hrightReplay

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBase_stable :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseFull
      ProgrammedGlobalChainKeygenBaseStableRelation := by
  exact relTriple_of_evalDist_eq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
    relTriple_coupledGlobalChainKeygen_withBase_fullCacheStable



set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalFilteredCausalKeygenState
    (view : ProgrammedGlobalChainKeygenView) : GlobalCausalHashState := by
  classical
  exact {
    cache := fun input =>
      if MerkleHashInput view.secretKey.parameter input then view.cache input
      else none
    keygenCache := view.cache
    revealed := fun _ => none
    probes := []
  }

@[simp]
theorem globalChainInputProbe?_encodingInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.encodingInput parameter leafIndex input) = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hchain : AtHashAddress parameter
        (.chain data.1 data.2.1 data.2.2.1)
        (Concrete.CacheView.encodingInput parameter leafIndex input) := by
      rw [hdata]
      simp [Concrete.CacheView.chainInput]
    have hencoding : AtHashAddress parameter (.encoding leafIndex)
        (Concrete.CacheView.encodingInput parameter leafIndex input) := by
      simp [Concrete.CacheView.encodingInput]
    have hdomain := atHashAddress_unique parameter
      (.chain data.1 data.2.1 data.2.2.1) (.encoding leafIndex)
      (Concrete.CacheView.encodingInput parameter leafIndex input) hchain
        hencoding
    simp at hdomain
  · rfl

@[simp]
theorem globalChainInputProbe?_leafInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.leafInput parameter leafIndex endpoints) = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter hdata
    simp at hdomain
  · rfl

def FilteredCacheExtensionRelation
    (leftBase left right : QueryCache HashSpec) : Prop :=
  ∀ input,
    left input = right input ∨
      (left input = leftBase input ∧ right input = none)

theorem FilteredCacheExtensionRelation.right_le_left
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right) :
    right ≤ left := by
  intro input output hright
  rcases hrel input with hagrees | ⟨_hbase, hnone⟩
  · rw [hagrees]
    exact hright
  · rw [hnone] at hright
    simp at hright

theorem FilteredCacheExtensionRelation.cacheQuery
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput) (output : Digest) :
    FilteredCacheExtensionRelation leftBase
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hrel candidate

theorem relTriple_randomOracle_run_of_current_eq_filtered
    (inputs : HashInput → Prop)
    (leftBase left right : QueryCache HashSpec)
    (input : HashInput) (hcurrent : left input = right input)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ Digest))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem simulate_eagerTrace_globalCausalHashQuery
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalHashQuery input).run state)).run =
      (fun result : Digest × QueryCache HashSpec =>
        ((result.1, state.setCache result.2),
          ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalHashQuery_run, simulateQ_map, WriterT.run_map',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [Functor.map_map]

def GlobalFilteredCausalStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalCausalHashState) : Prop :=
  HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightState.cache ∧
    FilteredCacheExtensionRelation left.cache leftCache rightState.cache ∧
    left.cache ≤ leftCache ∧
    rightState.keygenCache = right.1.cache ∧
    GlobalSigningRevealsAgree right.2 rightState

theorem GlobalSigningRevealsAgree.globalCausalRecordedState
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalSigningRevealsAgree table
      (globalCausalRecordedState secretKey input state) := by
  intro index value hvalue
  rw [globalCausalRecordedState_revealed] at hvalue
  exact hagrees index value hvalue

theorem GlobalFilteredCausalStateRelation.recordedStateSetCache
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (newLeft newRight : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      newLeft newRight)
    (hfiltered : FilteredCacheExtensionRelation left.cache newLeft newRight)
    (hle : leftCache ≤ newLeft) :
    GlobalFilteredCausalStateRelation left right newLeft
      { (globalCausalRecordedState secretKey input rightState) with
        cache := newRight } := by
  refine ⟨hagrees, hfiltered, hstate.2.2.1.trans hle, ?_, ?_⟩
  · simpa using hstate.2.2.2.1
  · exact ((hstate.2.2.2.2.globalCausalRecordedState secretKey input).setCache
      newRight)

theorem GlobalFilteredCausalStateRelation.recordedState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalCausalRecordedState secretKey input rightState) := by
  refine ⟨?_, ?_, hstate.2.2.1, ?_, ?_⟩
  · simpa using hstate.1
  · simpa using hstate.2.1
  · simpa using hstate.2.2.2.1
  · exact hstate.2.2.2.2.globalCausalRecordedState secretKey input

noncomputable def globalFilteredCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) : GlobalCausalHashState :=
  {
    cache := state.cache.cacheQuery input value
    keygenCache := state.keygenCache
    revealed := Function.update state.revealed index (some value)
    probes := (globalCausalRecordedState secretKey input state).probes
  }

theorem hashCachesAgreeOn_globalFilteredCausalRevealResultState
    {parameter : PublicParameter}
    {leftCache : QueryCache HashSpec} {rightState : GlobalCausalHashState}
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (hinput : ¬ GlobalSigningComparableHashInput parameter input) :
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index
        value).cache := by
  intro candidate hcandidate
  have hne : candidate ≠ input := by
    intro heq
    subst candidate
    exact hinput hcandidate
  unfold globalFilteredCausalRevealResultState
  change leftCache candidate =
    rightState.cache.cacheQuery input value candidate
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hagrees candidate hcandidate

theorem filteredCacheExtension_globalFilteredCausalRevealResultState
    {leftBase leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hfiltered : FilteredCacheExtensionRelation leftBase leftCache
      rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (hleft : leftCache input = some value) :
    FilteredCacheExtensionRelation leftBase leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index
        value).cache := by
  intro candidate
  change leftCache candidate =
      rightState.cache.cacheQuery input value candidate ∨
    (leftCache candidate = leftBase candidate ∧
      rightState.cache.cacheQuery input value candidate = none)
  by_cases heq : candidate = input
  · subst candidate
    left
    simp [hleft]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hfiltered candidate

theorem globalFilteredCausalRevealResultState_keygenCache_eq
    {rightState : GlobalCausalHashState} {keygenCache : QueryCache HashSpec}
    (hkeygen : rightState.keygenCache = keygenCache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) :
    (globalFilteredCausalRevealResultState secretKey input rightState index
      value).keygenCache = keygenCache := by
  unfold globalFilteredCausalRevealResultState
  exact hkeygen

theorem GlobalSigningRevealsAgree.globalFilteredCausalRevealResultState
    {table : GlobalChainValueIndex → Digest}
    {rightState : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (hvalue : table index = value) :
    GlobalSigningRevealsAgree table
      (globalFilteredCausalRevealResultState secretKey input rightState index
        value) := by
  intro candidate candidateValue hcand
  by_cases heq : candidate = index
  · subst candidate
    simp only [XmssSecurity.Generic.CappedChain.globalFilteredCausalRevealResultState,
      Function.update_self, Option.some.injEq] at hcand
    exact hvalue.trans hcand
  · have hright : rightState.revealed candidate = some candidateValue := by
      simpa only [XmssSecurity.Generic.CappedChain.globalFilteredCausalRevealResultState,
        Function.update_of_ne heq] using hcand
    exact hagrees candidate candidateValue hright

theorem GlobalFilteredCausalStateRelation.revealResultState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (hinput : ¬ GlobalSigningComparableHashInput
      left.secretKey.parameter input)
    (hleft : leftCache input = some value)
    (hvalue : right.2 index = value) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index
        value) := by
  exact ⟨
    hashCachesAgreeOn_globalFilteredCausalRevealResultState hstate.1 secretKey input
      index value hinput,
    filteredCacheExtension_globalFilteredCausalRevealResultState hstate.2.1 secretKey
      input index value hleft,
    hstate.2.2.1,
    globalFilteredCausalRevealResultState_keygenCache_eq hstate.2.2.2.1 secretKey input
      index value,
    hstate.2.2.2.2.globalFilteredCausalRevealResultState secretKey input index value
      hvalue⟩

def GlobalFilteredHashResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Digest × QueryCache HashSpec)
    (rightResult : (Digest × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

structure GlobalFilteredResultRelation (Output : Type)
    (parameter : PublicParameter)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Output × QueryCache HashSpec) : Prop where
  output_eq : leftResult.1 = rightResult.1
  caches_agree : HashCachesAgreeOn
    (GlobalSigningComparableHashInput parameter) leftResult.2 rightResult.2
  left_le : initialLeft ≤ leftResult.2
  right_le : initialRight ≤ rightResult.2
  filtered : FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2

theorem relTriple_globalRawHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput)
    (hinput : GlobalSigningComparableHashInput parameter input) :
    RelTriple ((randomOracle input).run left) ((randomOracle input).run right)
      (GlobalFilteredResultRelation Digest parameter leftBase left right) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ Digest))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        hagrees.cacheQuery (GlobalSigningComparableHashInput parameter)
          left right input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem relTriple_globalEncodingHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run right)
      (GlobalFilteredResultRelation Digest parameter leftBase left right) := by
  let input := Concrete.CacheView.encodingInput parameter leafIndex
    (message, randomness)
  change RelTriple
    ((fun result : Digest × QueryCache HashSpec =>
      (result.1, result.2)) <$> (randomOracle input).run left)
    ((fun result : Digest × QueryCache HashSpec =>
      (result.1, result.2)) <$> (randomOracle input).run right)
    (GlobalFilteredResultRelation Digest parameter leftBase left right)
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_globalRawHash_run_filtered parameter leftBase left right hagrees
      hfiltered input ⟨leafIndex, message, randomness, rfl⟩)
  intro leftResult rightResult hresult
  exact ⟨hresult.output_eq, hresult.caches_agree,
    hresult.left_le, hresult.right_le, hresult.filtered⟩


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem programmedGlobal_filteredKeygen_stateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalFilteredCausalStateRelation left right left.cache
      (globalFilteredCausalKeygenState right.1) := by
  classical
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.secretKey.parameter :=
        keygen_parameter_eq right.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.1.2
  refine ⟨?_, ?_, le_rfl, rfl, ?_⟩
  · intro input hinput
    obtain ⟨leafIndex, message, randomness, rfl⟩ := hinput
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey leafIndex (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter leafIndex (message, randomness)) = none at hleftNone
    have hnotMerkle : ¬ MerkleHashInput right.1.secretKey.parameter
        (Concrete.CacheView.encodingInput left.secretKey.parameter leafIndex
          (message, randomness)) := by
      rintro ⟨level, node, hmerkle⟩
      have hmerkleCanonical : AtHashAddress
          right.1.secretKey.parameter (.merkle level node)
          (Concrete.CacheView.encodingInput right.1.secretKey.parameter leafIndex
            (message, randomness)) := by
        simpa only [hparameter] using hmerkle
      have hencoding : AtHashAddress right.1.secretKey.parameter
          (.encoding leafIndex)
          (Concrete.CacheView.encodingInput right.1.secretKey.parameter leafIndex
            (message, randomness)) := by
        simp [Concrete.CacheView.encodingInput]
      have hdomain := atHashAddress_unique right.1.secretKey.parameter
        (.merkle level node) (.encoding leafIndex)
        (Concrete.CacheView.encodingInput right.1.secretKey.parameter leafIndex
          (message, randomness)) hmerkleCanonical hencoding
      simp at hdomain
    simpa [globalFilteredCausalKeygenState, hnotMerkle] using hleftNone
  · intro input
    by_cases hmerkle : MerkleHashInput right.1.secretKey.parameter input
    · left
      have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
        rw [hparameter]
        exact hmerkle
      simpa [globalFilteredCausalKeygenState, hmerkle] using
        htree.merkle input hmerkleLeft
    · right
      exact ⟨rfl, by simp [globalFilteredCausalKeygenState, hmerkle]⟩
  · intro index value hvalue
    simp [globalFilteredCausalKeygenState] at hvalue


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalCausalRevealHashQuery
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Digest × GlobalCausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  pure (value, globalFilteredCausalRevealResultState secretKey input state
    index value)

theorem simulate_eagerTrace_globalCausalRevealHashQuery
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalRevealHashQuery secretKey input state
        index)).run =
      pure ((table index,
        globalFilteredCausalRevealResultState secretKey input state index
          (table index)),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (table index)]) := by
  unfold globalCausalRevealHashQuery
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp


theorem Concrete.keygen_signWithEncoding_eq_base
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        leafIndex randomness encoding =
      Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
        leafIndex randomness encoding := by
  unfold Concrete.CacheReplay.signWithEncoding
  congr 1
  · funext chain
    calc
      Concrete.CacheReplay.signedChainValues largerCache keyResult.1.2
          leafIndex encoding chain =
        keygenChainValueTable keyResult.2 keyResult.1.2 chain
          (leafIndex, encoding chain) :=
        Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult largerCache hle leafIndex randomness encoding chain
      _ = Concrete.CacheReplay.signedChainValues keyResult.2 keyResult.1.2
          leafIndex encoding chain :=
        (Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult keyResult.2 le_rfl leafIndex randomness encoding
            chain).symm
  · exact (TreeCacheStable.authenticationPath_eq keyResult.1.2 keyResult.2
      hstable largerCache hle leafIndex).symm

noncomputable def globalFilteredCausalSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let randomness ← RevealProbeOracleSimulation.liftProbComp
    Concrete.signingRandomness
  let encoded ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash keyView.secretKey.parameter request.epoch
        request.message randomness)).run state.cache)
  let encodedState := { state with cache := encoded.2 }
  match Code.decodeDigest encoded.1 with
  | none => pure (none, encodedState)
  | some encoding => do
      let result ← (revealGlobalSignatureChains request encoding allChains
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.epoch randomness encoding)).run encodedState
      pure (some result.1, result.2)

noncomputable def globalFilteredCausalSignBoundedAttempts : Nat →
    ProgrammedGlobalChainKeygenView → SignRequest → GlobalCausalHashState →
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState)
  | 0, _keyView, _request, state => pure (none, state)
  | attempts + 1, keyView, request, state => do
      let result ← globalFilteredCausalSigningAttempt keyView request state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.2

noncomputable def globalFilteredCausalSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) :=
  globalFilteredCausalSignBoundedAttempts Code.signingAttemptLimit keyView request
    state

noncomputable def globalFilteredCausalSignTraceContinuation
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match result.1.1 with
  | some _signature => pure result
  | none =>
      (fun rest => (rest.1, result.2 ++ rest.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (globalFilteredCausalSignBoundedAttempts attempts keyView request
            result.1.2)).run

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalFilteredCausalSignBoundedAttempts (attempts + 1) keyView request
        state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run >>=
          globalFilteredCausalSignTraceContinuation attempts table keyView
            request := by
  rw [globalFilteredCausalSignBoundedAttempts, simulateQ_bind,
    WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨⟨signatureOption, resultState⟩, trace⟩
  cases signatureOption with
  | none =>
      simp only [globalFilteredCausalSignTraceContinuation]
      congr 1
  | some signature =>
      simp [globalFilteredCausalSignTraceContinuation]

def GlobalFilteredSigningResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

def GlobalFilteredSigningAttemptResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredSigningResultRelation left right leftResult rightResult ∧
    (leftResult.1 = none → rightResult.2 = [])

theorem relTriple_programmed_globalFilteredCausalSigningAttempt
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.sign left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (globalFilteredCausalSigningAttempt right.1 request
          rightState)).run)
      (GlobalFilteredSigningAttemptResultRelation left right) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.secretKey.parameter :=
        keygen_parameter_eq right.1.keyResult hrightKey
  rw [Concrete.sign_run_eq]
  unfold globalFilteredCausalSigningAttempt
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← Concrete.signingRandomness_eq]
  apply relTriple_bind (relTriple_refl Concrete.signingRandomness)
  intro leftRandomness rightRandomness hrandomness
  subst rightRandomness
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_globalEncodingHash_run_filtered
      left.secretKey.parameter left.cache leftCache rightState.cache
        hstate.1 hstate.2.1 request.epoch request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.output_eq
  rw [← hdigestEq]
  cases hdecode : Code.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      refine ⟨⟨rfl, hencoded.caches_agree, hencoded.filtered,
        hstate.2.2.1.trans hencoded.left_le, hstate.2.2.2.1, ?_⟩,
        fun _ => rfl⟩
      exact hstate.2.2.2.2.setCache rightEncoded.2
  | some encoding =>
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey request.epoch
              leftRandomness encoding)).run leftEncoded.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftEncoded.2
              left.secretKey request.epoch leftRandomness encoding,
                leftEncoded.2) := by
        simpa [ProgrammedGlobalChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.1.toStable.2.1 leftEncoded.2
            (hstate.2.2.1.trans hencoded.left_le) request.epoch
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply, simulateQ_pure,
        StateT.run_pure]
      rw [simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains]
      simp [Prod.map]
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningResultRelation
        GlobalFilteredCausalStateRelation
      let encodedState : GlobalCausalHashState :=
        { rightState with cache := rightEncoded.2 }
      let rightSignature := Concrete.CacheReplay.signWithEncoding
        right.1.cache right.1.secretKey request.epoch leftRandomness
          encoding
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.1.toStable.2.1 leftEncoded.2
          (hstate.2.2.1.trans hencoded.left_le) request.epoch
            leftRandomness encoding
      have hbase := keygenViews_signWithEncoding_eq_globalReveal
        left right hrel.1.toStable hleftSupport hrightSupport left.cache
          right.1.cache le_rfl le_rfl request leftRandomness encoding
            encodedState
      have hsignature :
          Concrete.CacheReplay.signWithEncoding leftEncoded.2 left.secretKey
              request.epoch leftRandomness encoding =
            (globalSignatureRevealResult right.2 request encoding allChains
              rightSignature encodedState).1 := hleftStable.trans hbase
      have hcachesFinal : HashCachesAgreeOn
          (GlobalSigningComparableHashInput left.secretKey.parameter)
          leftEncoded.2
          (globalSignatureRevealResult right.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.caches_agree
      have hfilteredFinal : FilteredCacheExtensionRelation left.cache
          leftEncoded.2
          (globalSignatureRevealResult right.2 request encoding allChains
            rightSignature encodedState).2.cache := by
        rw [globalSignatureRevealResult_cache]
        exact hencoded.filtered
      refine ⟨⟨congrArg some hsignature, hcachesFinal,
        hfilteredFinal,
        hstate.2.2.1.trans hencoded.left_le, ?_, ?_⟩, ?_⟩
      · rw [globalSignatureRevealResult_keygenCache]
        exact hstate.2.2.2.1
      · have hagrees := hstate.2.2.2.2.setCache rightEncoded.2
        exact hagrees.globalSignatureRevealResult request encoding allChains
          rightSignature
      · intro hnone
        simp at hnone

theorem relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    (attempts : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.signBoundedAttempts attempts left.secretKey
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (globalFilteredCausalSignBoundedAttempts attempts right.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right) := by
  induction attempts generalizing leftCache rightState with
  | zero =>
      simp only [Concrete.signBoundedAttempts,
        globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, hstate⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq_sign_bind attempts
        left.publicKey left.secretKey request.epoch request.message leftCache]
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ]
      apply relTriple_bind
        (relTriple_programmed_globalFilteredCausalSigningAttempt left right
          hrel hleftSupport hrightSupport leftCache rightState hstate request)
      intro leftAttempt rightAttempt hattempt
      rcases hattempt with ⟨hresult, hnil⟩
      rcases hresult with ⟨hoption, hstate'⟩
      cases hleft : leftAttempt.1 with
      | none =>
          have hright : rightAttempt.1.1 = none := by
            rw [← hoption, hleft]
          have htrace : rightAttempt.2 = [] := hnil hleft
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright, htrace]
          simpa using ih leftAttempt.2 rightAttempt.1.2 hstate'
      | some signature =>
          have hright : rightAttempt.1.1 = some signature := by
            rw [← hoption, hleft]
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright]
          apply relTriple_pure_pure
          exact ⟨hright.symm, hstate'⟩

theorem relTriple_programmed_globalFilteredCausalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.scheme.sign
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.epoch request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
        (globalFilteredCausalSigningQuery right.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right) := by
  simp only [Concrete.scheme, globalFilteredCausalSigningQuery]
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  apply relTriple_of_evalDist_eq_left
    (Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
      left.keyResult hleftKey hrel.1.2.1 leftCache hstate.2.2.1
        request.epoch request.message)
  rw [Concrete.cappedSign_eq]
  exact relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    Code.signingAttemptLimit left right hrel hleftSupport hrightSupport leftCache
      rightState hstate request


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalChainTableEdgeInput_not_signingComparable
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    ¬ GlobalSigningComparableHashInput parameter
      (globalChainTableEdgeInput parameter table edge) := by
  rintro ⟨leafIndex, message, randomness, hencoding⟩
  have hprobe : globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter edge.2.1 edge.1 edge.2.2
        (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) =
        some ((edge.1, edge.2.1, chainStepDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
    exact globalChainInputProbe?_chainInput parameter edge.2.1 edge.1 edge.2.2
      (table (edge.1, edge.2.1, chainStepDigit edge.2.2))
  unfold globalChainTableEdgeInput at hencoding
  rw [hencoding, globalChainInputProbe?_encodingInput] at hprobe
  simp at hprobe

end XmssSecurity.Generic.CappedChain

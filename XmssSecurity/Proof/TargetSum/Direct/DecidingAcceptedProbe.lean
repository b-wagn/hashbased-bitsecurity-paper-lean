import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneExpected

/-! Append the deciding probe only when the forged encoding is accepted. Winning first-lane
executions satisfy that condition, so rejected encodings incur no additional probe charge. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain FirstLaneOracleSimulation

def AcceptedPrefixFirstLaneEvent (key : ProgrammedGlobalChainKeygenView)
    (result : Forgery × SourceExactTracedState) : Prop :=
  PrefixFirstLaneEvent key result ∧
    (forgedEncoding result.2.1.1.1 key.secretKey.parameter result.1).isSome

noncomputable def publicAcceptedPrefixProbeExecution (fuel : ℕ) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld (Forgery × GlobalHighDirectTracedState) := do
  let result ← enforceHazardBound fuel (publicPrefixExecution adversary key edgeHigh)
  if (forgedEncoding result.2.causalState.cache key.secretKey.parameter result.1).isSome then
    let _ ← publicDecidingProbe result.1.epoch
      (signedEncoding result.2.causalState.cache key.secretKey.parameter
        result.2.attackerTrace.toSigningLog result.1.epoch)
      (prefixProbeEncoding result.2.causalState.cache key.secretKey.parameter result.1)
      result.1.signature.chainValue
    pure result
  else pure result

noncomputable def appendAcceptedPrefixProbe (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex :=
  if (forgedEncoding result.1.2.causalState.cache key.secretKey.parameter result.1.1).isSome
    then appendPrefixProbe base key (result.1, enforceHazardTrace fuel result.2)
    else (result.1, enforceHazardTrace fuel result.2)

theorem publicAcceptedPrefixProbeExecution_eager (fuel : ℕ) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest) :
    (simulateQ (eagerTraceImpl base) (publicAcceptedPrefixProbeExecution fuel adversary key edgeHigh)).run =
      appendAcceptedPrefixProbe fuel base key <$>
        (simulateQ (eagerTraceImpl base) (publicPrefixExecution adversary key edgeHigh)).run := by
  unfold publicAcceptedPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind']
  rw [simulate_eagerTrace_enforceHazardBound]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  by_cases haccepted : (forgedEncoding result.1.2.causalState.cache key.secretKey.parameter result.1.1).isSome
  · simp only [haccepted, if_true, simulateQ_bind, WriterT.run_bind', publicDecidingProbe_eager,
      pure_bind, simulateQ_pure, WriterT.run_pure', map_pure]
    simp [appendAcceptedPrefixProbe, haccepted, appendPrefixProbe, prefixProbeResult, Prod.map]
    rfl
  · simp [haccepted, appendAcceptedPrefixProbe, simulateQ_pure, Prod.map]
    rfl

theorem hazardCount_appendAcceptedPrefixProbe (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendAcceptedPrefixProbe fuel base key result).2 =
      min fuel (hazardCount result.2) +
        if (forgedEncoding result.1.2.causalState.cache key.secretKey.parameter result.1.1).isSome
          then 1 else 0 := by
  unfold appendAcceptedPrefixProbe
  split <;> simp_all [appendPrefixProbe, prefixProbeResult, hazardCount_append,
    decidingProbeResult_hazardCount, hazardCount_enforceHazardTrace]

theorem hazardCount_appendAcceptedPrefixProbe_le (fuel : ℕ) (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendAcceptedPrefixProbe fuel base key result).2 ≤ fuel + 1 := by
  rw [hazardCount_appendAcceptedPrefixProbe]
  split_ifs <;> omega

theorem sourceFinish_firstLane_forgedEncoding_some
    (key : ProgrammedGlobalChainKeygenView) (prefixResult : Forgery × SourceExactTracedState)
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningDecidingFirstLaneEvent (key, execution)) :
    (forgedEncoding prefixResult.2.1.1.1 key.secretKey.parameter prefixResult.1).isSome := by
  rw [sourcePrefixFinish, support_map] at hfinish
  obtain ⟨verified, hverified, rfl⟩ := hfinish
  rw [forgedEncoding_eq_of_cache_le _ verified.2 (xmssRom_cache_le _ _ _ hverified)
    key.secretKey.parameter prefixResult.1 hcached]
  rcases hevent with hencoding | ⟨_hwin, hrevealed⟩
  · obtain ⟨encoding, hdecode⟩ := hencoding.1.forgery_decode
    change forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]
  · obtain ⟨encoding, hdecode, _⟩ := hrevealed
    change forgedEncoding verified.2 key.secretKey.parameter prefixResult.1 = some encoding at hdecode
    simp [hdecode]

theorem sourceFirstLaneEvent_implies_acceptedPrefixEvent (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hcached : prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
      prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none)
    (execution : (Forgery × Bool) × SourceExactTracedState)
    (hfinish : execution ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningDecidingFirstLaneEvent (key, execution)) :
    AcceptedPrefixFirstLaneEvent key prefixResult :=
  ⟨sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix hcached
      execution hfinish hevent,
    sourceFinish_firstLane_forgedEncoding_some key prefixResult hcached execution hfinish hevent⟩

theorem forgedEncoding_eq_of_comparableCaches (leftCache rightCache : QueryCache HashSpec)
    (parameter : PublicParameter)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (forgery : Forgery) :
    forgedEncoding leftCache parameter forgery = forgedEncoding rightCache parameter forgery := by
  unfold forgedEncoding
  rw [encodingHash_eq_of_comparableCaches _ _ _ hcaches]

theorem acceptedPrefixEvent_probability_le_enforcedHit_afterKeygen
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (left : ProgrammedGlobalChainKeygenView) (right : BaseHighKey)
    (hkey : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen) :
    RelTriple (sourcePrefixExecution adversary left)
      ((simulateQ (eagerTraceImpl right.1.2)
        (publicAcceptedPrefixProbeExecution D adversary right.1.1 right.2)).run)
      (fun leftResult rightResult => AcceptedPrefixFirstLaneEvent left leftResult →
        CombinedHit right.1.2 (enforceHazardTrace (D + 1) rightResult.2)) := by
  rw [publicAcceptedPrefixProbeExecution_eager]
  have hpk : left.publicKey = right.1.1.publicKey := hkey.1.toStable.1.2.1
  have hcoupling := relTriple_sourceExact_firstLane_adversary_boundedHit_direct D D
    le_rfl adversary left right hkey hleftSupport hrightSupport (hD left.publicKey)
  have hrightProgram : (simulateQ (eagerTraceImpl right.1.2)
      (publicPrefixExecution adversary right.1.1 right.2)).run =
    (simulateQ (eagerTraceImpl right.1.2)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2)
        (adversary.main left.publicKey)).run
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)))).run := by
    unfold publicPrefixExecution
    rw [hpk]
  rw [hrightProgram, ← id_map (sourcePrefixExecution adversary left)]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_with_support hcoupling)
  intro leftResult rightResult hresult hevent
  obtain ⟨hrel, _hleft, hright⟩ := hresult
  rw [enforceHazardTrace_eq_self_of_count_le _ _
    (hazardCount_appendAcceptedPrefixProbe_le D right.1.2 right.1.1 rightResult)]
  rcases hrel with ⟨hforgery, hgood, hcount⟩ | hhit
  · have hparameter := programmedGlobal_secretKey_parameter_eq left right hkey hleftSupport hrightSupport
    obtain ⟨_monitor, _hmonitor, _hagrees, _hrevealed, hcausal, _hretained⟩ := hgood.1.1
    change GlobalFilteredCausalStateRelation left right.1 leftResult.2.1.1.1
      rightResult.1.2.causalState at hcausal
    have hencoding : forgedEncoding leftResult.2.1.1.1 left.secretKey.parameter leftResult.1 =
        forgedEncoding rightResult.1.2.causalState.cache right.1.1.secretKey.parameter rightResult.1.1 := by
      rw [hparameter, ← hforgery]
      exact forgedEncoding_eq_of_comparableCaches _ _ _ hcausal.1 _
    have haccepted : (forgedEncoding rightResult.1.2.causalState.cache
        right.1.1.secretKey.parameter rightResult.1.1).isSome := by
      rw [← hencoding]
      exact hevent.2
    rw [appendAcceptedPrefixProbe, if_pos haccepted,
      enforceHazardTrace_eq_self_of_count_le _ D hcount]
    rw [hpk] at hright
    have hcovered := globalFirstLaneAdversary_support_returnedCovered right.1.1 right.1.2
      right.2 (adversary.main right.1.1.publicKey) rightResult hright
    have hhit := prefixFirstLaneEvent_good_implies_hit left right hkey hleftSupport hrightSupport
      leftResult rightResult hforgery hgood hcovered hevent.1
    exact hhit
  · unfold appendAcceptedPrefixProbe
    split
    · exact CombinedHit.append_of_prefix _ _ _ hhit
    · exact hhit

theorem sourceAcceptedPrefixProgram_coupling (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicAcceptedPrefixProbeExecution D adversary))
      (fun left right => AcceptedPrefixFirstLaneEvent left.1 left.2 →
        CombinedHit right.1.1.2 (enforceHazardTrace (D + 1) right.2.2)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleftSupport, hrightSupport⟩ := hkeys
  apply relTriple_bind (acceptedPrefixEvent_probability_le_enforcedHit_afterKeygen
    adversary D hD left right hkey hleftSupport
      (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hrightSupport))
  intro leftResult rightResult hresult
  exact relTriple_pure_pure hresult

theorem acceptedPrefixFirstLane_probability_le_expected (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedCoupledHazards (D + 1) (publicAcceptedPrefixProbeExecution D adversary) := by
  calc
    _ ≤ Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (D + 1) result.2.2) |
        coupledFirstLaneProgram (publicAcceptedPrefixProbeExecution D adversary)] := by
      apply probEvent_le_of_relTriple (sourceAcceptedPrefixProgram_coupling adversary D hD)
      intro left right hrel hevent
      exact hrel hevent
    _ ≤ _ := coupled_enforcedHit_probability_le_expected (D + 1)
      (publicAcceptedPrefixProbeExecution D adversary)

theorem decidingFirstLane_probability_le_acceptedPrefix_of_cached (adversary : Adversary)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] := by
  rw [decidingFirstLane_probability_eq_source, sourceProgram_eq_prefix_finish]
  apply probEvent_bind_le_probEvent
  intro prefixPair hprefixPair hnone
  unfold sourcePrefixProgram at hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨key, hkey, hprefixPair⟩ := hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨prefixResult, hprefix, hpure⟩ := hprefixPair
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst prefixPair
  apply probEvent_eq_zero
  intro finalResult hfinal hevent
  rw [mem_support_bind_iff] at hfinal
  obtain ⟨execution, hfinish, hpure⟩ := hfinal
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst finalResult
  exact hnone (sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix
    (hcached key hkey prefixResult hprefix) execution hfinish hevent)

theorem decidingFirstLane_probability_le_expected_acceptedProbe_of_cached
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedCoupledHazards (D + 1) (publicAcceptedPrefixProbeExecution D adversary) :=
  (decidingFirstLane_probability_le_acceptedPrefix_of_cached adversary hcached).trans
    (acceptedPrefixFirstLane_probability_le_expected adversary D hD)

def CoupledPrefixForgedEncodingAccepted
    (result : BaseHighKey × ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)) :
    Prop :=
  (forgedEncoding result.2.1.2.causalState.cache result.1.1.1.secretKey.parameter result.2.1.1).isSome

theorem coupledAcceptedPrefixProbe_eq_map (fuel : ℕ) (adversary : Adversary) :
    coupledFirstLaneProgram (publicAcceptedPrefixProbeExecution fuel adversary) =
      (fun result => (result.1, appendAcceptedPrefixProbe fuel result.1.1.2 result.1.1.1 result.2)) <$>
        coupledFirstLaneProgram (publicPrefixExecution adversary) := by
  unfold coupledFirstLaneProgram
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro key
  rw [publicAcceptedPrefixProbeExecution_eager]
  simp only [bind_map_left]

theorem expectedCoupledHazards_acceptedProbe_eq (fuel : ℕ) (adversary : Adversary) :
    expectedCoupledHazards (fuel + 1) (publicAcceptedPrefixProbeExecution fuel adversary) =
      expectedCoupledHazards fuel (publicPrefixExecution adversary) +
        Pr[CoupledPrefixForgedEncodingAccepted | coupledFirstLaneProgram (publicPrefixExecution adversary)] := by
  classical
  unfold expectedCoupledHazards
  rw [coupledAcceptedPrefixProbe_eq_map, tsum_probOutput_map_mul]
  have hweight (result : BaseHighKey ×
      ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)) :
      ((min (fuel + 1)
        (hazardCount (appendAcceptedPrefixProbe fuel result.1.1.2 result.1.1.1 result.2).2) : ℕ) : ℝ≥0∞) =
        ((min fuel (hazardCount result.2.2) : ℕ) : ℝ≥0∞) +
          if CoupledPrefixForgedEncodingAccepted result then 1 else 0 := by
    rw [min_eq_right (hazardCount_appendAcceptedPrefixProbe_le fuel _ _ _),
      hazardCount_appendAcceptedPrefixProbe, Nat.cast_add]
    by_cases haccepted : CoupledPrefixForgedEncodingAccepted result <;>
      simp_all [CoupledPrefixForgedEncodingAccepted]
  simp_rw [hweight, mul_add]
  rw [ENNReal.tsum_add]
  congr 1
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  split_ifs <;> simp

/-- The final deciding probe is charged to the probability that its encoding is accepted,
instead of adding one unconditional query to every execution. -/
theorem decidingFirstLane_probability_le_expected_prefix_and_accepted
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        (expectedCoupledHazards D (publicPrefixExecution adversary) +
          Pr[CoupledPrefixForgedEncodingAccepted | coupledFirstLaneProgram (publicPrefixExecution adversary)]) := by
  have h := decidingFirstLane_probability_le_expected_acceptedProbe_of_cached adversary D hD hcached
  rwa [expectedCoupledHazards_acceptedProbe_eq] at h

theorem decidingFirstLane_withForgedEncodingQuery_probability_le_expected_prefix_and_accepted
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[WinningDecidingFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace (Direct.withForgedEncodingQuery adversary)] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        (expectedCoupledHazards (D + 1) (publicPrefixExecution (Direct.withForgedEncodingQuery adversary)) +
          Pr[CoupledPrefixForgedEncodingAccepted |
            coupledFirstLaneProgram (publicPrefixExecution (Direct.withForgedEncodingQuery adversary))]) :=
  decidingFirstLane_probability_le_expected_prefix_and_accepted (Direct.withForgedEncodingQuery adversary)
    (D + 1) (Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD)
    (sourcePrefixExecution_withForgedEncodingQuery_cached adversary)

/-- info: 'XmssSecurity.TargetSum.Deciding.decidingFirstLane_probability_le_expected_prefix_and_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_expected_prefix_and_accepted

/-- info: 'XmssSecurity.TargetSum.Deciding.expectedCoupledHazards_acceptedProbe_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedCoupledHazards_acceptedProbe_eq

end XmssSecurity.TargetSum.Deciding

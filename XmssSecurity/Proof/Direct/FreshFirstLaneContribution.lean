import XmssSecurity.Proof.Direct.FreshPrefixProjection

/-! Retain the actual fresh first-lane winning probability in the loss decomposition.
It can be bounded further without charging the accepted prefix a second time. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain Direct

noncomputable def freshFirstLaneProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => SourcePrefixForgedEncodingFresh result.1 ∧
      SourceWinningDecidingFirstLaneEvent (result.1.1, result.2) | do
    let prefixPair ← sourcePrefixProgram adversary
    let result ← sourcePrefixFinish prefixPair.1 prefixPair.2
    pure (prefixPair, result)]

theorem freshFirstLaneProbability_le_acceptance (adversary : Adversary) :
    freshFirstLaneProbability adversary ≤
      Checksum.acceptanceProbability * forgedEncodingFreshProbability adversary := by
  rw [forgedEncodingFreshProbability_eq_source]
  exact sourceFirstLane_fresh_prefix_event_probability_le (sourcePrefixProgram adversary)
    Prod.fst Prod.snd SourcePrefixForgedEncodingFresh (fun _ _ h => h)

theorem decidingFirstLane_probability_le_accepted_add_fresh_contribution (adversary : Adversary) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] +
        freshFirstLaneProbability adversary := by
  let head := sourcePrefixProgram adversary
  let tail := fun pair : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState) =>
    sourcePrefixFinish pair.1 pair.2
  let win := fun (pair : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) result =>
    SourceWinningDecidingFirstLaneEvent (pair.1, result)
  rw [decidingFirstLane_probability_eq_source, sourceProgram_eq_prefix_finish,
    freshFirstLaneProbability, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro pair
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  by_cases hpair : pair ∈ support head
  · by_cases haccepted : AcceptedPrefixFirstLaneEvent pair.1 pair.2
    · rw [if_pos haccepted]
      exact le_add_right (mul_le_of_le_one_right zero_le probEvent_le_one)
    rw [if_neg haccepted, zero_add]
    by_cases hfresh : SourcePrefixForgedEncodingFresh pair
    · simp only [hfresh, true_and, le_refl]
    simp only [hfresh, false_and]
    have hzero : Pr[win pair | tail pair] = 0 := by
      apply probEvent_eq_zero
      intro result hresult hevent
      unfold head sourcePrefixProgram at hpair
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
      obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
      apply haccepted
      apply sourceFirstLaneEvent_implies_acceptedPrefixEvent adversary key hkey prefixResult hprefix _
        result hresult hevent
      have hparameter := keygen_parameter_eq key.keyResult
        (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)
      change key.publicKey.parameter = key.secretKey.parameter at hparameter
      change prefixResult.2.1.1.1 (Concrete.CacheView.encodingInput key.publicKey.parameter
        prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none at hfresh
      rw [hparameter] at hfresh
      exact hfresh
    change Pr[= pair | head] * Pr[win pair | tail pair] ≤ _
    rw [hzero, mul_zero]
    exact zero_le
  · change Pr[= pair | head] * _ ≤ _
    rw [probOutput_eq_zero_of_not_mem_support hpair]
    simp only [zero_mul, ite_self, zero_add, le_refl]

/-- info: 'XmssSecurity.Deciding.decidingFirstLane_probability_le_accepted_add_fresh_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_accepted_add_fresh_contribution

end XmssSecurity.Deciding

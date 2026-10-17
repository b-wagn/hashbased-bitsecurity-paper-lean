import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries

/-! A forged encoding cached on every execution requires at least one expected
encoding query, paid by direct queries or the signer. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

theorem one_le_cachedEncodingInputCount_of_cached (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (payload : Message × Randomness)
    (hcached : cache (Concrete.CacheView.encodingInput parameter leafIndex payload) ≠ none) :
    1 ≤ cachedEncodingInputCount cache parameter := by
  cases hentry : cache (Concrete.CacheView.encodingInput parameter leafIndex payload) with
  | none => exact (hcached hentry).elim
  | some output =>
      let entry : (input : HashSpec.Domain) × HashSpec.Range input :=
        ⟨Concrete.CacheView.encodingInput parameter leafIndex payload, output⟩
      have hsubset : ({entry} : Set ((input : HashSpec.Domain) × HashSpec.Range input)) ⊆
          cachedEncodingInputSet cache parameter := by
        intro candidate hcand
        simp only [Set.mem_singleton_iff] at hcand
        subst candidate
        exact ⟨hentry, by simp [entry]⟩
      simpa only [cachedEncodingInputCount, Set.encard_singleton, ENat.toENNReal_one] using
        ENat.toENNReal_mono (Set.encard_mono hsubset)

namespace Direct

theorem one_le_expectedEncodingQueries_of_cached (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (hcached : ∀ result ∈ support ((simulateQ romImpl
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
      result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
        (result.1.1.message, result.1.1.signature.randomness)) ≠ none) :
    1 ≤ expectedSimulatedQueryCount romImpl
      (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 := by
  have hupper := expectedResource_le_initial_add_expectedSimulatedQueryCount romImpl
    (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
    (fun cache => cachedEncodingInputCount cache keyResult.1.2.parameter)
    (cachedEncodingInputCount_romImpl_step_le keyResult.1.2.parameter)
    (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2
  rw [Concrete.keygen_cachedEncodingInputCount_eq_zero keyResult hkey, zero_add] at hupper
  apply le_trans _ hupper
  apply le_expected_of_support
  · exact tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)
  · intro result hresult
    exact one_le_cachedEncodingInputCount_of_cached _ _ _ _ (hcached result hresult)

theorem one_le_expectedDirectEncoding_add_signer_of_cached (adversary : Adversary)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ result ∈ support ((simulateQ romImpl
        (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
        result.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
          (result.1.1.message, result.1.1.signature.randomness)) ≠ none) :
    1 ≤ expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary := by
  apply le_trans _ (expectedPrefixEncodingQueries_le adversary)
  unfold Deciding.expectedPrefixEncodingQueries
  apply le_expected_of_support
  · exact tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _)
  · intro keyResult hkey
    exact one_le_expectedEncodingQueries_of_cached adversary keyResult hkey (hcached keyResult hkey)

/-- info: 'XmssSecurity.TargetSum.Direct.one_le_expectedDirectEncoding_add_signer_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_le_expectedDirectEncoding_add_signer_of_cached

end Direct
end XmssSecurity.TargetSum

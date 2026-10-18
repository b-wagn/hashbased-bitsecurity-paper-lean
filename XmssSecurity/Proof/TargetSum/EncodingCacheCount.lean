import XmssSecurity.Proof.Generic.SignCacheHitProbability
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Exact encoding-cache accounting: fresh encoding inputs add one entry, while
nonencoding queries leave the count unchanged. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum

theorem cachedEncodingInputSet_cacheQuery_eq_insert
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : Digest)
    (hencoding : (encodingInputLeafIndex? parameter input).isSome)
    (hfresh : cache input = none) :
    cachedEncodingInputSet (cache.cacheQuery input output) parameter =
      insert ⟨input, output⟩ (cachedEncodingInputSet cache parameter) := by
  apply Set.Subset.antisymm
  · simpa only [hencoding, if_true] using
      cachedEncodingInputSet_cacheQuery_subset cache parameter input output
  · intro entry hentry
    rcases hentry with rfl | hentry
    · exact ⟨QueryCache.cacheQuery_self _ _ _, hencoding⟩
    · exact ⟨QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hentry.1, hentry.2⟩

theorem cachedEncodingInputCount_cacheQuery_eq_add_one
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : Digest)
    (hencoding : (encodingInputLeafIndex? parameter input).isSome)
    (hfresh : cache input = none) :
    cachedEncodingInputCount (cache.cacheQuery input output) parameter =
      cachedEncodingInputCount cache parameter + 1 := by
  have hnotMem : (⟨input, output⟩ : (t : HashSpec.Domain) × HashSpec.Range t) ∉
      cachedEncodingInputSet cache parameter := by
    intro hentry
    have hcached := hentry.1
    change cache input = some output at hcached
    rw [hfresh] at hcached
    cases hcached
  unfold cachedEncodingInputCount
  rw [cachedEncodingInputSet_cacheQuery_eq_insert cache parameter input output hencoding hfresh,
    Set.encard_insert_of_notMem hnotMem]
  simpa only [ENat.toENNReal_one] using
    ENat.toENNReal_add (cachedEncodingInputSet cache parameter).encard 1

theorem cachedEncodingInputCount_cacheQuery_eq_of_nonencoding
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (input : HashInput) (output : Digest)
    (hinput : encodingInputLeafIndex? parameter input = none) :
    cachedEncodingInputCount (cache.cacheQuery input output) parameter =
      cachedEncodingInputCount cache parameter := by
  have hset : cachedEncodingInputSet (cache.cacheQuery input output) parameter =
      cachedEncodingInputSet cache parameter := by
    ext ⟨candidate, answer⟩
    by_cases heq : candidate = input
    · subst candidate
      simp [cachedEncodingInputSet, hinput]
    · simp [cachedEncodingInputSet, QueryCache.cacheQuery_of_ne _ _ heq]
  simp only [cachedEncodingInputCount, hset]

theorem cachedEncodingInputCount_eq_of_agree
    (parameter : PublicParameter) (left right : QueryCache HashSpec)
    (hagrees : ∀ input, (encodingInputLeafIndex? parameter input).isSome → left input = right input) :
    cachedEncodingInputCount left parameter = cachedEncodingInputCount right parameter := by
  have hset : cachedEncodingInputSet left parameter = cachedEncodingInputSet right parameter := by
    ext ⟨input, output⟩
    by_cases hencoding : (encodingInputLeafIndex? parameter input).isSome
    · simp only [cachedEncodingInputSet, Set.mem_setOf_eq, QueryCache.mem_toSet,
        hencoding, and_true, hagrees input hencoding]
    · simp [cachedEncodingInputSet, hencoding]
  simp only [cachedEncodingInputCount, hset]

theorem cachedEncodingInputCount_eq_zero_of_no_encodingInputs
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (hempty : ∀ leafIndex payload,
      cache (Concrete.CacheView.encodingInput parameter leafIndex payload) = none) :
    cachedEncodingInputCount cache parameter = 0 := by
  have hset : cachedEncodingInputSet cache parameter = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨input, output⟩ ⟨hcached, hencoding⟩
    obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
    obtain ⟨payload, rfl⟩ := exists_encodingInput_of_encodingInputLeafIndex?_eq_some
      parameter input leafIndex hleaf
    change cache (Concrete.CacheView.encodingInput parameter leafIndex payload) = some output at hcached
    rw [hempty] at hcached
    cases hcached
  simp only [cachedEncodingInputCount, hset, Set.encard_empty, ENat.toENNReal_zero]

/-- info: 'XmssSecurity.TargetSum.cachedEncodingInputCount_cacheQuery_eq_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cachedEncodingInputCount_cacheQuery_eq_add_one

end XmssSecurity.TargetSum

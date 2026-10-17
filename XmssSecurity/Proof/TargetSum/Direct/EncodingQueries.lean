import XmssSecurity.Proof.TargetSum.Direct.Prehit

/-!
# Encoding queries and the prehit potential

Only encoding-domain queries can increase the prehit potential. This separates their charge
from structural queries, which is needed when combining the two losses without double counting.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace XmssSecurity.TargetSum.Direct

def IsDirectEncodingQuery (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr input) => (encodingInputLeafIndex? parameter input).isSome
  | _ => False

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsDirectEncodingQuery parameter) :=
  Classical.decPred _

theorem isDirectHashQuery_of_encoding (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (h : IsDirectEncodingQuery parameter input) :
    IsDirectHashQuery input := by
  rcases input with (uniform | hash) | request
  · exact h.elim
  · exact isDirectHashQuery_hash hash
  · exact h.elim

theorem hash_query_cache_subset_at_input (publicKey : PublicKey) (secretKey : SecretKey)
    (input : HashInput) (initialCache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey (.inl (.inr input))).run initialCache)) :
    result.2.toSet ⊆ insert ⟨input, result.1⟩ initialCache.toSet := by
  change result ∈ support ((randomOracle (spec := HashSpec) input).run initialCache) at hresult
  cases hcache : initialCache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact QueryCache.toSet_cacheQuery_subset_insert initialCache input output
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcache, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Set.subset_insert _ _

theorem untracedEncodingEntryCount_le_of_nonencoding_insert
    (initialCache finalCache : QueryCache HashSpec) (parameter : PublicParameter)
    (trace : SigningCacheTrace) (input : HashInput) (output : HashOutput)
    (hsubset : finalCache.toSet ⊆ insert ⟨input, output⟩ initialCache.toSet)
    (hnone : encodingInputLeafIndex? parameter input = none) :
    untracedEncodingEntryCount finalCache parameter trace ≤
      untracedEncodingEntryCount initialCache parameter trace := by
  apply ENat.toENNReal_mono
  apply Set.encard_mono
  intro entry hentry
  obtain ⟨hcache, leaf, hleaf, hnot⟩ := hentry
  rcases hsubset hcache with heq | hold
  · subst entry
    simp [hnone] at hleaf
  · exact ⟨hold, leaf, hleaf, hnot⟩

theorem untracedEncodingEntryCount_hash_query_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : HashInput) (initialCache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey (.inl (.inr input))).run initialCache)) :
    untracedEncodingEntryCount result.2 secretKey.parameter trace ≤
      untracedEncodingEntryCount initialCache secretKey.parameter trace +
        if IsDirectEncodingQuery secretKey.parameter (.inl (.inr input)) then 1 else 0 := by
  have hsubset := hash_query_cache_subset_at_input publicKey secretKey input initialCache result hresult
  split
  · exact untracedEncodingEntryCount_le_of_subset_insert initialCache result.2 secretKey.parameter
      trace ⟨input, result.1⟩ hsubset
  · rename_i hnonencoding
    rw [add_zero]
    apply untracedEncodingEntryCount_le_of_nonencoding_insert initialCache result.2
      secretKey.parameter trace input result.1 hsubset
    cases hleaf : encodingInputLeafIndex? secretKey.parameter input with
    | none => rfl
    | some leaf =>
      exfalso
      apply hnonencoding
      change (encodingInputLeafIndex? secretKey.parameter input).isSome = true
      rw [hleaf]
      rfl

theorem encodingQuery_structuralTarget_fixed (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hencoding : IsDirectEncodingQuery secretKey.parameter (.inl (.inr input))) :
    keygenStructuralTargetInput secretKey cache input = input := by
  by_contra hne
  exact encodingHashQuery_structuralQuery_disjoint secretKey cache (.inr input) ⟨hencoding, hne⟩

end XmssSecurity.TargetSum.Direct

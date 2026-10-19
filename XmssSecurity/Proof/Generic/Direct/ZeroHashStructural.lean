import XmssSecurity.Proof.Generic.Direct.StructuralQueries

/-! A hash-free adversary prefix, including its final encoding query, creates no structural
collision. The signer only queries the encoding domain in the precomputed reference scheme. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

theorem zeroHash_prefix_no_structural_collision (adversary : Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) (publicKey : PublicKey)
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (result : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ romImpl (adversaryPhase adversary publicKey secretKey)).run cache)) :
    ¬ Rom.AdaptiveFreshDigestCollisionWith cache result.2
      (keygenStructuralTargetInput secretKey cache) := by
  classical
  let event := fun result : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
    Rom.AdaptiveFreshDigestCollisionWith cache result.2 (keygenStructuralTargetInput secretKey cache)
  have hprob : Pr[event | (simulateQ romImpl
      (adversaryPhase adversary publicKey secretKey)).run cache] = 0 := by
    apply le_antisymm _ zero_le
    have hcount : expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput secretKey cache input ≠ input)
        (adversaryPhase adversary publicKey secretKey) cache = 0 := by
      apply le_antisymm _ zero_le
      rw [Direct.expectedStructuralQueries_adversaryPhase_eq]
      have h := Direct.expectedDirectEncoding_add_structural_le publicKey secretKey cache cache
        (adversary.main publicKey) 0 (hzero publicKey)
      exact le_trans le_add_self (by simpa using h)
    have hbound := Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
      (adversaryPhase adversary publicKey secretKey) cache
      (keygenStructuralTargetInput secretKey cache) event (fun _ _ h => h)
    simpa only [hcount, ENNReal.zero_div] using hbound
  exact probEvent_eq_zero_iff.mp hprob result hresult

theorem no_collision_cacheQuery_fixed (initialCache cache : QueryCache HashSpec)
    (hle : initialCache ≤ cache) (target : HashInput → HashInput) (added : HashInput)
    (digest : Digest) (hfresh : cache added = none) (hfixed : target added = added)
    (hnone : ¬ Rom.AdaptiveFreshDigestCollisionWith initialCache cache target) :
    ¬ Rom.AdaptiveFreshDigestCollisionWith initialCache
      (cache.cacheQuery added digest) target := by
  classical
  rintro ⟨input, output, targetOutput, hcached, hinitial, htarget, hvalues⟩
  have hinput : input ≠ added := by
    intro heq
    change initialCache (target input) = some targetOutput at htarget
    rw [heq, hfixed] at htarget
    exact Option.some_ne_none _ ((hle htarget).symm.trans hfresh)
  have htargetNe : target input ≠ added := by
    intro heq
    change initialCache (target input) = some targetOutput at htarget
    rw [heq] at htarget
    exact Option.some_ne_none _ ((hle htarget).symm.trans hfresh)
  apply hnone
  refine ⟨input, output, targetOutput, ?_, hinitial, htarget, ?_⟩
  · simpa only [QueryCache.cacheQuery_of_ne _ _ hinput] using hcached
  · change Concrete.CacheView.digestAt (cache.cacheQuery added digest) input =
      Concrete.CacheView.digestAt (cache.cacheQuery added digest) (target input) at hvalues
    unfold Concrete.CacheView.digestAt at hvalues ⊢
    simpa only [QueryCache.cacheQuery_of_ne _ _ hinput,
      QueryCache.cacheQuery_of_ne _ _ htargetNe] using hvalues

theorem no_structural_collision_cacheQuery_encoding (secretKey : SecretKey)
    (initialCache cache : QueryCache HashSpec) (hle : initialCache ≤ cache)
    (leaf : LeafIndex) (message : Message) (randomness : Randomness) (digest : Digest)
    (hfresh : cache (Concrete.CacheView.encodingInput secretKey.parameter leaf
      (message, randomness)) = none)
    (hnone : ¬ Rom.AdaptiveFreshDigestCollisionWith initialCache cache
      (keygenStructuralTargetInput secretKey initialCache)) :
    ¬ Rom.AdaptiveFreshDigestCollisionWith initialCache
      (cache.cacheQuery (Concrete.CacheView.encodingInput secretKey.parameter leaf
        (message, randomness)) digest) (keygenStructuralTargetInput secretKey initialCache) := by
  apply no_collision_cacheQuery_fixed initialCache cache hle _ _ digest hfresh _ hnone
  apply Direct.encodingQuery_structuralTarget_fixed
  simp [Direct.IsDirectEncodingQuery, encodingInputLeafIndex?_encodingInput]

end XmssSecurity.Generic.Deciding

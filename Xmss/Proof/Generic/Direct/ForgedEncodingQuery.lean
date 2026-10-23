import Xmss.Proof.Generic.Direct.Basic
import Xmss.Proof.Generic.DetailedExecution

/-!
# The adversary with the forged encoding query

`withForgedEncodingQuery adversary` runs `adversary` and then hashes the encoding input of its
own forgery before returning it. This costs one extra direct hash query, and does not change the
game: the verifier's first hash query is that same input, so it is answered from the cache.
-/

open OracleComp OracleSpec

namespace Xmss.Generic.Direct

variable [Code]

/-- The encoding input of a forgery under a public key. -/
abbrev forgeryEncodingInput (publicKey : PublicKey) (forgery : Forgery) : HashInput :=
  CacheView.encodingInput publicKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)

/-- The adversary that, after producing its forgery, hashes the forgery's own encoding input. -/
noncomputable def withForgedEncodingQuery (adversary : Adversary) : Adversary :=
  ⟨fun publicKey => do
    let forgery ← adversary.main publicKey
    let _ ← liftM ((OracleWorld + SigningSpec).query (.inl (.inr
      (CacheView.encodingInput publicKey.parameter forgery.epoch
        (forgery.message, forgery.signature.randomness)))))
    pure forgery⟩

theorem withForgedEncodingQuery_isDirectQueryBound (adversary : Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    IsDirectQueryBound (withForgedEncodingQuery adversary) (D + 1) := by
  intro publicKey
  refine isQueryBoundP_bind (hD publicKey) fun forgery _ => ?_
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr Nat.one_pos, fun _ => by simp⟩

/-- The adversary phase of the modified adversary: the original phase, then one hash query of
the forgery's encoding input, which leaves the signing log unchanged. -/
theorem run_simulateQ_withForgedEncodingQuery (adversary : Adversary) (secretKey : SecretKey)
    (publicKey : PublicKey) :
    (simulateQ (forwardOracles + signingOracle precomputedScheme secretKey)
        ((withForgedEncodingQuery adversary).main publicKey)).run =
      (simulateQ (forwardOracles + signingOracle precomputedScheme secretKey)
        (adversary.main publicKey)).run >>= fun result =>
      liftM (OracleWorld.query (.inr (forgeryEncodingInput publicKey result.1))) >>= fun _ =>
        pure result := by
  simp only [withForgedEncodingQuery, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    WriterT.run_bind', WriterT.run_pure']
  refine bind_congr fun result => ?_
  change (Prod.map id (result.2 ++ ·)) <$>
    (((fun answer : Digest => (answer, (∅ : QueryLog SigningSpec))) <$>
      liftM (OracleWorld.query (.inr (forgeryEncodingInput publicKey result.1)))) >>=
        fun answer => Prod.map id (answer.2 ++ ·) <$> pure (result.1, ∅)) = _
  simp only [map_bind, bind_map_left, map_pure, Prod.map_apply, id_eq, List.empty_eq,
    List.append_nil]
  rfl

/-! ## The random oracle answers a repeated input from the cache -/

omit [Code] in
/-- After one random-oracle call on `input`, the returned cache holds the returned answer. -/
theorem randomOracle_run_cached (input : HashInput) (cache : QueryCache HashSpec)
    (result : Digest × QueryCache HashSpec)
    (hresult : result ∈ support
      (((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) input).run
        cache)) :
    result.2 input = some result.1 := by
  cases hcache : cache input with
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcache, support_pure,
        Set.mem_singleton_iff] at hresult
      subst hresult
      exact hcache
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hcache, support_map] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      exact QueryCache.cacheQuery_self _ _ _

omit [Code] in
/-- Two consecutive random-oracle calls on the same input: the second is a cache hit. -/
theorem randomOracle_bind_randomOracle_same {β : Type} (input : HashInput)
    (continuation : Digest → Digest → StateT (QueryCache HashSpec) ProbComp β) :
    ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) input >>=
        fun first => randomOracle input >>= fun second => continuation first second) =
      (randomOracle input >>= fun first => continuation first first) := by
  apply StateT.ext
  intro cache
  simp only [StateT.run_bind]
  cases hcache : cache input with
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcache]
      simp only [pure_bind, QueryImpl.withCaching_run_some _ hcache]
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hcache]
      simp only [bind_map_left,
        QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache input _), pure_bind]

/-! ## The verifier's first query -/

/-- The verifier after its encoding hash. -/
noncomputable def verifyAfterDigest (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (digest : Digest) : OracleComp HashSpec Bool :=
  match Code.decodeDigest digest with
  | none => pure false
  | some encoding => do
      let endpoints ← Verify.recoverEndpoints publicKey.parameter leafIndex encoding signature
      let leaf ← Hashing.leafHash publicKey.parameter leafIndex endpoints
      Verify.verifyAfterLeaf publicKey leafIndex signature leaf

theorem concrete_verify_eq_query_bind (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool) =
      (liftM (HashSpec.query (CacheView.encodingInput publicKey.parameter leafIndex
        (message, signature.randomness))) >>= fun output =>
          verifyAfterDigest publicKey leafIndex signature (output)) := by
  simp only [Verify.verify_eq_decode]
  unfold Hashing.encodingHash Hashing.tweakableHash Hashing.oracleHash
    verifyAfterDigest
  refine bind_congr fun output => ?_
  cases Code.decodeDigest (output) <;> rfl

/-- The verifier under the random oracle: the encoding query, then the rest. -/
theorem simulateQ_romImpl_scheme_verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    simulateQ romImpl (precomputedScheme.verify publicKey leafIndex message signature) =
      ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
        (CacheView.encodingInput publicKey.parameter leafIndex
          (message, signature.randomness)) >>= fun output =>
        simulateQ randomOracle (verifyAfterDigest publicKey leafIndex signature
          (output))) := by
  change simulateQ (unifFwdImpl HashSpec +
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
    (liftM (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)) = _
  rw [QueryImpl.simulateQ_add_liftM_right, concrete_verify_eq_query_bind, simulateQ_bind,
    simulateQ_spec_query]

omit [Code] in
theorem romImpl_inr (input : HashInput) :
    romImpl (.inr input) =
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) input := rfl

/-! ## The game is unchanged -/

theorem simulateQ_romImpl_detailedGameAfterKeygen_withForgedEncodingQuery (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) :
    simulateQ romImpl (detailedGameAfterKeygen precomputedScheme (withForgedEncodingQuery adversary)
        publicKey secretKey) =
      simulateQ romImpl (detailedGameAfterKeygen precomputedScheme adversary publicKey secretKey) := by
  unfold detailedGameAfterKeygen
  rw [run_simulateQ_withForgedEncodingQuery]
  simp only [simulateQ_bind, bind_assoc]
  refine bind_congr fun result => ?_
  rcases result with ⟨forgery, signingLog⟩
  simp only [simulateQ_spec_query, simulateQ_pure, pure_bind, romImpl_inr,
    simulateQ_romImpl_scheme_verify, bind_assoc]
  exact randomOracle_bind_randomOracle_same _ _

theorem simulateQ_romImpl_detailedGameCore_withForgedEncodingQuery (adversary : Adversary) :
    simulateQ romImpl (detailedGameCore precomputedScheme (withForgedEncodingQuery adversary)) =
      simulateQ romImpl (detailedGameCore precomputedScheme adversary) := by
  unfold detailedGameCore
  simp only [simulateQ_bind]
  refine bind_congr fun keys => ?_
  rcases keys with ⟨publicKey, secretKey⟩
  exact simulateQ_romImpl_detailedGameAfterKeygen_withForgedEncodingQuery adversary publicKey
    secretKey

/-- The game's outcome and final cache are unchanged: the verifier's first hash query is the same
input, now a cache hit. -/
theorem detailedGameWithCache_withForgedEncodingQuery (adversary : Adversary) :
    detailedGameWithCache precomputedScheme (withForgedEncodingQuery adversary) =
      detailedGameWithCache precomputedScheme adversary := by
  unfold detailedGameWithCache
  rw [simulateQ_romImpl_detailedGameCore_withForgedEncodingQuery]

theorem forgeAdvantage_withForgedEncodingQuery (adversary : Adversary) :
    forgeAdvantage precomputedScheme (withForgedEncodingQuery adversary) =
      forgeAdvantage precomputedScheme adversary := by
  rw [forgeAdvantage_eq_detailedGameWithCache, forgeAdvantage_eq_detailedGameWithCache,
    detailedGameWithCache_withForgedEncodingQuery]

/-! ## The forgery's encoding input is cached after the adversary phase -/

/-- After the modified adversary's phase, its forgery's encoding input is cached. -/
theorem adversaryPhase_withForgedEncodingQuery_cached (adversary : Adversary)
    (publicKey : PublicKey) (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      ((simulateQ (forwardOracles + signingOracle precomputedScheme secretKey)
        ((withForgedEncodingQuery adversary).main publicKey)).run)).run cache)) :
    prefixResult.2 (CacheView.encodingInput publicKey.parameter prefixResult.1.1.epoch
      (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none := by
  rw [run_simulateQ_withForgedEncodingQuery, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hprefix
  obtain ⟨⟨result, middleCache⟩, _, hquery⟩ := hprefix
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, romImpl_inr, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hquery
  obtain ⟨⟨output, finalCache⟩, hcall, rfl⟩ := hquery
  have hcached := randomOracle_run_cached _ _ _ hcall
  simp only [forgeryEncodingInput] at hcached
  simp [hcached]

end Xmss.Generic.Direct

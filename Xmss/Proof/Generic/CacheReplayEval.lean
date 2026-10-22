import Xmss.Proof.Generic.CacheVerify
import Xmss.Proof.Generic.LazyScheme
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec

namespace Xmss.Generic.CacheReplay

open Hashing

variable [Code]

def answer (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  (cache input).getD 0

def answerFn (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => answer cache input

omit [Code] in
@[simp]
theorem answer_eq_digestAt (cache : QueryCache HashSpec) (input : HashInput) :
    answer cache input = CacheView.digestAt cache input := by
  cases hcache : cache input <;> simp [answer, CacheView.digestAt, hcache]

omit [Code] in
@[simp]
theorem eval_oracleHash (cache : QueryCache HashSpec) (input : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Hashing.oracleHash input : OracleComp HashSpec Digest) = answer cache input := by
  simpa [Hashing.oracleHash, answerFn] using
    evalWithAnswerFn_query (answerFn cache) input

@[simp]
theorem eval_tweakableHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Hashing.tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      CacheView.tweakableHash cache parameter domain payload := by
  simp [Hashing.tweakableHash, CacheView.tweakableHash]

@[simp]
theorem eval_encodingHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn (answerFn cache)
      (Hashing.encodingHash parameter leafIndex message randomness : OracleComp HashSpec Digest) =
      CacheView.encodingHash cache parameter leafIndex (message, randomness) := by
  simp [Hashing.encodingHash, CacheView.encodingHash, CacheView.encodingInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Wots.chainWalk parameter leafIndex chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) position steps value := by
  induction steps with
  | zero => simp [Wots.chainWalk, Wots.walk]
  | succ steps ih =>
      simp only [Wots.chainWalk, evalWithAnswerFn_bind, ih, Wots.walk]
      by_cases hposition : position + steps < chainLength - 1
      · simp [hposition, Hashing.chainHash, CacheView.chainStep,
          CacheView.chainInput, CacheView.tweakableHash]
      · simp [hposition, CacheView.chainStep]

@[simp]
theorem eval_recoverChain (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Verify.recoverChain parameter leafIndex chain digit value : OracleComp HashSpec Digest) =
      Wots.recoverChain (CacheView.chainStep cache parameter leafIndex chain) digit value := by
  simp [Verify.recoverChain, Wots.recoverChain]

omit [Code] in
@[simp]
theorem eval_sequenceFin (cache : QueryCache HashSpec) {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn (answerFn cache) (sequenceFin computation) =
      fun index => evalWithAnswerFn (answerFn cache) (computation index) := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n ih =>
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

@[simp]
theorem eval_recoverEndpoints (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (encoding : Encoding)
    (signature : Signature) :
    evalWithAnswerFn (answerFn cache)
      (Verify.recoverEndpoints parameter leafIndex encoding signature :
        OracleComp HashSpec (ChainIndex → Digest)) =
      Xmss.Generic.recoveredEndpoints
        (fun chain => CacheView.chainStep cache parameter leafIndex chain)
        encoding signature.chainValue := by
  funext chain
  simp [Verify.recoverEndpoints, Xmss.Generic.recoveredEndpoints]

@[simp]
theorem eval_leafHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    evalWithAnswerFn (answerFn cache)
      (Hashing.leafHash parameter leafIndex endpoints : OracleComp HashSpec Digest) =
      CacheView.leafHash cache parameter leafIndex endpoints := by
  simp [Hashing.leafHash, CacheView.leafHash, CacheView.leafInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_nodeHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Hashing.nodeHash parameter level node left right : OracleComp HashSpec Digest) =
      CacheView.merkleHash cache parameter level node left right := by
  simp [Hashing.nodeHash, CacheView.merkleHash, CacheView.merkleInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_oneTimePublicKey (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    evalWithAnswerFn (answerFn cache)
      (Wots.oneTimePublicKey parameter secret leafIndex :
        OracleComp HashSpec (ChainIndex → Digest)) =
      oneTimePublicKey cache parameter secret leafIndex := by
  funext chain
  simp [Wots.oneTimePublicKey, oneTimePublicKey]

@[simp]
theorem eval_leafAt (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    evalWithAnswerFn (answerFn cache)
      (Merkle.leafAt parameter secret leafIndex : OracleComp HashSpec Digest) =
      leafAt cache parameter secret leafIndex := by
  simp [Merkle.leafAt, leafAt]

@[simp]
theorem eval_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (answerFn cache)
      (Merkle.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  induction levels generalizing node with
  | zero => simp [Merkle.treeNode_zero_eq, treeNode_zero_eq]
  | succ levels ih =>
      rw [Merkle.treeNode_succ_eq]
      simp only [evalWithAnswerFn_bind, ih, treeNode_succ_eq]
      split <;> simp_all

/-! Key generation materializes the secret key's vectors using `evalWithAnswerFn (replayHash cache)`.
The `eval_*` lemmas and `Vector.getElem_ofFn` identify each stored digest with its
`CacheView`/`CacheReplay` value. -/

omit [Code] in
theorem answerFn_eq_replayHash (cache : QueryCache HashSpec) :
    answerFn cache = Keygen.replayHash cache := rfl

@[simp]
theorem eval_replayHash_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (Keygen.replayHash cache)
      (Wots.chainWalk parameter leafIndex chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) position steps value := by
  rw [← answerFn_eq_replayHash]
  exact eval_chainWalk cache parameter leafIndex chain position steps value

@[simp]
theorem eval_replayHash_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (Keygen.replayHash cache)
      (Merkle.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  rw [← answerFn_eq_replayHash]
  exact eval_treeNode cache parameter secret levels node

@[simp]
theorem precomputedSecretKey_chainValue (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) :
    (Keygen.precomputedSecretKey parameter secret cache).chainValue leafIndex chain digit =
      Wots.walk (CacheView.chainStep cache parameter leafIndex chain) 0 digit.val
        (secret leafIndex chain) := by
  simp [Xmss.SecretKey.chainValue, Keygen.precomputedSecretKey]

@[simp]
theorem precomputedSecretKey_treeValue (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (height : MerkleHeight) (node : MerkleNode) :
    (Keygen.precomputedSecretKey parameter secret cache).treeValue height node =
      treeNode cache parameter secret height.val node := by
  simp [Xmss.SecretKey.treeValue, Keygen.precomputedSecretKey]

def signedChainValues (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => Wots.walk
    (CacheView.chainStep cache secretKey.parameter leafIndex chain) 0
    (encoding chain).val (secretKey.chainStart leafIndex chain)

def authenticationPath (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) : Fin treeHeight → Digest :=
  fun level => treeNode cache secretKey.parameter secretKey.chainStart level.val
    (Merkle.authenticationPathNode leafIndex level)

def signWithEncoding (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, signedChainValues cache secretKey leafIndex encoding,
    authenticationPath cache secretKey leafIndex⟩

theorem precomputedSignedChainValues_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (encoding : Encoding) :
    (fun chain => (Keygen.precomputedSecretKey parameter secret cache).chainValue leafIndex chain (encoding chain)) =
      signedChainValues cache (Keygen.precomputedSecretKey parameter secret cache)
        leafIndex encoding := by
  funext chain
  exact precomputedSecretKey_chainValue parameter secret cache leafIndex chain (encoding chain)

theorem precomputedAuthenticationPath_eq (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (cache : QueryCache HashSpec) (leafIndex : LeafIndex) :
    (fun level : Fin treeHeight => (Keygen.precomputedSecretKey parameter secret cache).treeValue
        level.castSucc (Merkle.authenticationPathNode leafIndex level)) =
      authenticationPath cache (Keygen.precomputedSecretKey parameter secret cache)
        leafIndex := by
  funext level
  exact precomputedSecretKey_treeValue parameter secret cache level.castSucc
    (Merkle.authenticationPathNode leafIndex level)

@[simp]
theorem eval_authenticationRoot (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (leafIndex : LeafIndex) (signature : Signature)
    (levels : Nat) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Verify.authenticationRoot parameter leafIndex signature levels leaf :
        OracleComp HashSpec Digest) =
      Merkle.ascend (CacheView.nodeHash cache parameter leafIndex)
        (Verify.signaturePath signature) 0 levels leaf := by
  induction levels with
  | zero => simp [Verify.authenticationRoot, Merkle.ascend]
  | succ levels ih =>
      simp only [Verify.authenticationRoot, evalWithAnswerFn_bind, ih, Merkle.ascend,
        Nat.zero_add]
      by_cases hlevel : levels < treeHeight
      · by_cases hbit : leafIndex.val.testBit levels = true
        · simp [Verify.authenticationNodeHash, CacheView.nodeHash, hlevel, hbit,
            Hashing.nodeHash, CacheView.nodeInput, CacheView.authenticationNodePayload,
            CacheView.tweakableHash]
        · simp [Verify.authenticationNodeHash, CacheView.nodeHash, hlevel, hbit,
            Hashing.nodeHash, CacheView.nodeInput, CacheView.authenticationNodePayload,
            CacheView.tweakableHash]
      · simp [Verify.authenticationNodeHash, CacheView.nodeHash, hlevel]

@[simp]
theorem eval_verifyAfterLeaf (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Verify.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool) =
      decide (Merkle.ascend (CacheView.nodeHash cache publicKey.parameter leafIndex)
        (Verify.signaturePath signature) 0 treeHeight leaf = publicKey.root) := by
  simp [Verify.verifyAfterLeaf]

theorem eval_verify (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (hcached : ∃ output, cache (CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = some output) :
    evalWithAnswerFn (answerFn cache)
      (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool) =
      Verify.verifyFromCache cache publicKey leafIndex message signature := by
  classical
  simp only [Verify.verify_eq_decode]
  unfold Verify.verifyFromCache
  rw [CacheView.decodedEncoding_eq_of_cached hcached]
  simp only [evalWithAnswerFn_bind, eval_encodingHash]
  cases Code.decodeDigest
    (CacheView.encodingHash cache publicKey.parameter leafIndex (message, signature.randomness)) <;> simp

omit [Code] in
theorem randomOracle_query_caches (input : HashInput)
    (initialCache : QueryCache HashSpec) (output : Digest)
    (finalCache : QueryCache HashSpec)
    (hmem : (output, finalCache) ∈
      support ((randomOracle (spec := HashSpec) input).run initialCache)) :
    finalCache input = some output := by
  cases hcache : initialCache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hmem
      obtain ⟨sampled, _, hresult⟩ := hmem
      cases hresult
      exact QueryCache.cacheQuery_self initialCache input output
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      exact hcache

omit [Code] in
theorem randomOracle_cache_le {α : Type} (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ randomOracle computation).run initialCache)) :
    initialCache ≤ result.2 := by
  exact OracleComp.simulateQ_run_preservesInv randomOracle
    (fun cache => initialCache ≤ cache)
    (by
      intro input cache hcache queryResult hquery
      exact hcache.trans
        (QueryImpl.withCaching_cache_le uniformSampleImpl input cache
          queryResult hquery))
    computation initialCache le_rfl result hmem

omit [Code] in
/-- Rerunning a lazy random-oracle computation against any extension of a cache produced by a
successful first run is deterministic and leaves the larger cache unchanged. -/
theorem randomOracle_rerun_largerCache_eq_pure_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    (simulateQ randomOracle computation).run largerCache =
      pure (result, largerCache) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache largerCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, _hcache⟩ := hmem
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache
          (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hlarger]
      simp only [pure_bind]
      exact ih output middleCache resultCache largerCache result hrest hle

omit [Code] in
/-- Replaying a lazy-oracle execution against its final cache reproduces its result. -/
theorem eval_answerFn_finalCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α) (initialCache finalCache : QueryCache HashSpec)
    (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    evalWithAnswerFn (answerFn finalCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ finalCache :=
        randomOracle_cache_le (next output) middleCache (result, finalCache) hrest
      have hfinal : finalCache input = some output := hmiddleLe hmiddle
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn finalCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec Digest) = output := by
        simpa [Hashing.oracleHash, answer, hfinal] using
          eval_oracleHash finalCache input
      rw [hqueryEval]
      exact ih output middleCache finalCache result hrest

omit [Code] in
/-- Replaying an execution against any extension of its final cache reproduces its result. -/
theorem eval_answerFn_largerCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    evalWithAnswerFn (answerFn largerCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn largerCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec Digest) = output := by
        simpa [Hashing.oracleHash, answer, hlarger] using
          eval_oracleHash largerCache input
      rw [hqueryEval]
      exact ih output middleCache resultCache result hrest hle

/-- A verification run records its encoding query. -/
theorem verify_run_encodingInput_cached
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (initialCache finalCache : QueryCache HashSpec)
    (result : Bool)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle
        (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run
          initialCache)) :
    ∃ output, finalCache (CacheView.encodingInput publicKey.parameter leafIndex
      (message, signature.randomness)) = some output := by
  simp only [Verify.verify_eq_decode] at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hrest⟩ := hmem
  have hle : digestCache ≤ finalCache := randomOracle_cache_le _ digestCache _ hrest
  unfold Hashing.encodingHash Hashing.tweakableHash Hashing.oracleHash at hdigest
  exact ⟨digest, hle (randomOracle_query_caches (tweakableHashInput publicKey.parameter
    (.encoding leafIndex) (encodingPayload message signature.randomness)) _ _ _
    (by simpa using hdigest))⟩

/-- A signing attempt records its encoding query. -/
theorem precomputedSignAttempt_run_encodingInput_cached
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (initialCache finalCache : QueryCache HashSpec)
    (result : Option Signature)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle
        (Signing.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run initialCache)) :
    ∃ output, finalCache (CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness)) = some output := by
  unfold Signing.precomputedSignAttempt at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hrest⟩ := hmem
  have hle : digestCache ≤ finalCache := randomOracle_cache_le _ digestCache _ hrest
  unfold Hashing.encodingHash Hashing.tweakableHash Hashing.oracleHash at hdigest
  exact ⟨digest, hle (randomOracle_query_caches (tweakableHashInput secretKey.parameter
    (.encoding leafIndex) (encodingPayload message randomness)) _ _ _
    (by simpa using hdigest))⟩

theorem verifyFromCache_eq_of_mem_support
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) (initialCache finalCache : QueryCache HashSpec)
    (result : Bool)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle
        (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run
          initialCache)) :
    Verify.verifyFromCache finalCache publicKey leafIndex message signature = result := by
  rw [← eval_verify _ _ _ _ _ (verify_run_encodingInput_cached publicKey leafIndex message
    signature initialCache finalCache result hmem)]
  exact eval_answerFn_finalCache_eq_of_mem_support
    (Verify.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)
    initialCache finalCache result hmem

end Xmss.Generic.CacheReplay

import Xmss.Proof.Generic.ChainOraclePresampling

open OracleComp OracleSpec

namespace Xmss.Generic.CacheReplay

variable [Code]

theorem verify_true_chain_query_cached_as_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding) (chain : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (encoding chain).val)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Verify.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : CacheView.decodedEncoding largerCache publicKey.parameter leafIndex
        (message, signature.randomness) = some encoding)
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (CacheView.chainInput publicKey.parameter leafIndex chain
        ⟨(encoding chain).val + offset, by omega⟩
        (Wots.walk (CacheView.chainStep largerCache publicKey.parameter leafIndex chain)
          (encoding chain).val offset (signature.chainValue chain))) = some output := by
  simp only [Verify.verify_eq_decode] at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hactualDecode : Code.decodeDigest digest with
  | none =>
      simp only [hactualDecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some actualEncoding =>
      have hdigestResultLe : digestCache ≤ resultCache :=
        randomOracle_cache_le
          (do
            let endpoints ← Verify.recoverEndpoints publicKey.parameter leafIndex
              actualEncoding signature
            let leaf ← Hashing.leafHash publicKey.parameter leafIndex endpoints
            Verify.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          digestCache (true, resultCache) (by
            simpa only [hactualDecode] using hafterDigest)
      have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
        (Hashing.encodingHash publicKey.parameter leafIndex message signature.randomness :
          OracleComp HashSpec Digest)
        initialCache digestCache largerCache digest hdigest (hdigestResultLe.trans hle)
      rw [eval_encodingHash] at hdigestEval
      have hencoding : actualEncoding = encoding := by
        have hdecode' := CacheView.decodeDigest_of_decodedEncoding hdecode
        rw [hdigestEval, hactualDecode] at hdecode'
        exact Option.some.inj hdecode'
      subst actualEncoding
      simp only [hactualDecode] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterDigest
      obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hafterDigest
      have hendpointsResultLe : endpointsCache ≤ resultCache :=
        randomOracle_cache_le
          (do
            let leaf ← Hashing.leafHash publicKey.parameter leafIndex endpoints
            Verify.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          endpointsCache (true, resultCache) hafterEndpoints
      unfold Verify.recoverEndpoints at hendpoints
      obtain ⟨beforeCache, afterCache, value, hchain, hchainLe⟩ :=
        sequenceFin_component_support_in_largerCache
          (fun index => Verify.recoverChain publicKey.parameter leafIndex index
            (encoding index) (signature.chainValue index) :
            ChainIndex → OracleComp HashSpec Digest)
          chain digestCache endpointsCache largerCache endpoints hendpoints
          (hendpointsResultLe.trans hle)
      unfold Verify.recoverChain at hchain
      exact chainWalk_query_cached_in_largerCache publicKey.parameter leafIndex chain
        (encoding chain).val (chainLength - 1 - (encoding chain).val)
        (signature.chainValue chain) offset hoffset (by omega) beforeCache afterCache
        largerCache value hchain hchainLe

end Xmss.Generic.CacheReplay

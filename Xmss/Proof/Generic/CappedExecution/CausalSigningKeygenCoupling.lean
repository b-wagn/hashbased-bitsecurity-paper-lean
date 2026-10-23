import Xmss.Proof.Generic.CacheAgreement
import Xmss.Proof.Generic.ChainWalkCache
import Xmss.Proof.Generic.BoundedSignProbability
import Xmss.Proof.Generic.PrecomputedBoundedSignProbability
import Xmss.Proof.Generic.CappedExecution.TreeCacheStability
import Xmss.Proof.Generic.KeygenCache
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace Xmss.Generic.CappedExecution

variable [Code]

omit [Code] in
theorem simulate_sequenceFin_run_eq_pure
    {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (values : Fin n → α)
    (hrun : ∀ index,
      (simulateQ randomOracle (computation index)).run cache =
        pure (values index, cache)) :
    (simulateQ randomOracle (sequenceFin computation)).run cache =
      pure (values, cache) := by
  induction n with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact Fin.elim0 index
      simp [sequenceFin, hvalues]
  | succ n ih =>
      rw [sequenceFin, simulateQ_bind, StateT.run_bind, hrun 0]
      simp only [pure_bind]
      rw [simulateQ_bind, StateT.run_bind,
        ih (fun index => computation index.succ)
          (fun index => values index.succ) (fun index => hrun index.succ)]
      simp only [pure_bind, simulateQ_pure, StateT.run_pure]
      congr
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

theorem Keygen.keygen_signedChainValues_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (encoding : Encoding) :
    (simulateQ randomOracle
      (Signing.signedChainValues keyResult.1.2 leafIndex encoding)).run
        largerCache =
      pure (CacheReplay.signedChainValues largerCache
        keyResult.1.2 leafIndex encoding, largerCache) := by
  let values : ChainIndex → Digest := fun chain =>
    keygenChainValueTable keyResult.2 keyResult.1.2 chain
      (leafIndex, encoding chain)
  have hrun : ∀ chain,
      (simulateQ randomOracle
        (Wots.chainWalk keyResult.1.2.parameter leafIndex chain 0
          (encoding chain).val
          (keyResult.1.2.chainStart leafIndex chain))).run largerCache =
        pure (values chain, largerCache) := by
    intro chain
    exact simulate_chainWalk_run_eq_pure_of_table_matches largerCache
      keyResult.1.2 chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain)
      (keygenChainValueTable_seedsMatch keyResult.2 keyResult.1.2 chain)
      ((Keygen.keygenChainValueTable_edgesMatch
        keyResult hkeyResult chain).mono hle)
      leafIndex (encoding chain).val (encoding chain).isLt
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun chain => Wots.chainWalk keyResult.1.2.parameter leafIndex chain 0
      (encoding chain).val (keyResult.1.2.chainStart leafIndex chain))
    largerCache values hrun
  have hvalues : values = CacheReplay.signedChainValues
      largerCache keyResult.1.2 leafIndex encoding := by
    funext chain
    exact Keygen.keygen_chainWalk_eq_of_cache_le keyResult hkeyResult
      largerCache hle leafIndex chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  simpa [Signing.signedChainValues, hvalues] using hsequence

theorem TreeCacheStable.authenticationPath_run_eq_pure
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (leafIndex : LeafIndex) :
    (simulateQ randomOracle
      (Signing.authenticationPath secretKey leafIndex)).run largerCache =
      pure (CacheReplay.authenticationPath largerCache secretKey leafIndex,
        largerCache) := by
  have hrun : ∀ level,
      (simulateQ randomOracle
        (Merkle.treeNode secretKey.parameter secretKey.chainStart level.val
          (Merkle.authenticationPathNode leafIndex level) :
          OracleComp HashSpec Digest)).run largerCache =
        pure (CacheReplay.treeNode cache secretKey.parameter
          secretKey.chainStart level.val
            (Merkle.authenticationPathNode leafIndex level), largerCache) := by
    intro level
    exact hstable level.val (Merkle.authenticationPathNode leafIndex level)
      (by omega) (authenticationPathNode_subtreeValid leafIndex level)
        largerCache hle
  have hsequence := simulate_sequenceFin_run_eq_pure
    (fun level => Merkle.treeNode secretKey.parameter secretKey.chainStart
      level.val (Merkle.authenticationPathNode leafIndex level)) largerCache
    (CacheReplay.authenticationPath cache secretKey leafIndex) hrun
  rw [hstable.authenticationPath_eq secretKey cache largerCache hle leafIndex]
    at hsequence
  simpa [Signing.authenticationPath] using hsequence

theorem Keygen.keygen_signWithEncoding_run_eq_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) :
    (simulateQ randomOracle
      (Signing.signWithEncoding keyResult.1.2 leafIndex randomness encoding)).run
        largerCache =
      pure (CacheReplay.signWithEncoding largerCache keyResult.1.2
        leafIndex randomness encoding, largerCache) := by
  unfold Signing.signWithEncoding
  rw [simulateQ_bind, StateT.run_bind,
    Keygen.keygen_signedChainValues_run_eq_pure keyResult hkeyResult
      largerCache hle leafIndex encoding]
  simp only [pure_bind]
  rw [simulateQ_bind, StateT.run_bind,
    hstable.authenticationPath_run_eq_pure keyResult.1.2 keyResult.2
      largerCache hle leafIndex]
  simp [CacheReplay.signWithEncoding]

private theorem replaySignature_eq_of_components (cache : QueryCache HashSpec)
    (left right : SecretKey) (hp : left.parameter = right.parameter)
    (hs : left.chainStart = right.chainStart) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) :
    CacheReplay.signWithEncoding cache left leafIndex randomness encoding =
      CacheReplay.signWithEncoding cache right leafIndex randomness encoding := by
  unfold CacheReplay.signWithEncoding
  refine congrArg₂ (Xmss.Signature.mk randomness) ?_ ?_
  · funext chain
    simp only [CacheReplay.signedChainValues, hp, hs]
  · funext level
    simp only [CacheReplay.authenticationPath, hp, hs]

theorem Signing.precomputedSignAttempt_materialized_run_eq_signAttempt
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    evalDist ((simulateQ randomOracle
      (Signing.precomputedSignAttempt
        (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message randomness : OracleComp HashSpec (Option Signature))).run
        largerCache) =
      evalDist ((simulateQ randomOracle
        (Signing.signAttempt keyResult.1.2 leafIndex message randomness :
          OracleComp HashSpec (Option Signature))).run largerCache) := by
  have hmaterialized :=
    Keygen.oldKeygen_support_materializedPrecomputedKeygen keyResult hkeyResult
  have hconsistent := Keygen.precomputedKeygen_support_consistent
    (Keygen.materializeCachedKeyResult keyResult) hmaterialized
  dsimp only [Keygen.materializeCachedKeyResult] at hconsistent
  unfold Signing.precomputedSignAttempt Signing.signAttempt
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  simp only [Keygen.materializePrecomputation_parameter]
  apply evalDist_bind_congr
  intro digestResult hdigestResult
  have hdigestLe := CacheReplay.randomOracle_cache_le
    (Hashing.encodingHash keyResult.1.2.parameter leafIndex message randomness)
      largerCache digestResult (by
        simpa [Keygen.materializePrecomputation] using hdigestResult)
  cases hdecode : Code.decodeDigest digestResult.1 with
  | none =>
    simp only
  | some encoding =>
    simp only
    rw [simulateQ_map, StateT.run_map]
    rw [Keygen.keygen_signWithEncoding_run_eq_pure keyResult hkeyResult
      hstable digestResult.2 (hle.trans hdigestLe)
      leafIndex randomness encoding]
    simp only [Functor.map]
    have hsignature := hconsistent digestResult.2 (hle.trans hdigestLe)
      leafIndex randomness encoding
    have hsignature' : Signing.precomputedSignWithEncoding
      (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
        leafIndex randomness encoding =
      CacheReplay.signWithEncoding digestResult.2 keyResult.1.2
        leafIndex randomness encoding :=
      hsignature.trans (replaySignature_eq_of_components _ _ _
        (Keygen.materializePrecomputation_parameter _ _)
        (Keygen.materializePrecomputation_chainStart _ _) _ _ _)
    rw [hsignature']
    rfl

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
theorem Signing.evalDist_precomputedSignBoundedAttempts_materialized_eq
    (attempts : Nat)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) :
    evalDist ((simulateQ romImpl
      (Signing.precomputedSignBoundedAttempts attempts
        (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message)).run largerCache) =
      evalDist ((simulateQ romImpl
        (Signing.signBoundedAttempts attempts keyResult.1.2 leafIndex message)).run
          largerCache) := by
  induction attempts generalizing largerCache with
  | zero => rfl
  | succ attempts ih =>
      rw [Signing.precomputedSignBoundedAttempts_run_succ_eq,
        Signing.signBoundedAttempts_run_succ_eq]
      apply evalDist_bind_congr
      intro randomness _hrandomness
      calc
        evalDist ((simulateQ randomOracle
              (Signing.precomputedSignAttempt
                (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
                  leafIndex message randomness :
                    OracleComp HashSpec (Option Signature))).run largerCache >>=
            Signing.precomputedSignBoundedAttemptsContinuation attempts
              (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
                leafIndex message) =
            evalDist ((simulateQ randomOracle
              (Signing.signAttempt keyResult.1.2 leafIndex message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Signing.precomputedSignBoundedAttemptsContinuation attempts
                (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
                  leafIndex message) := by
          rw [evalDist_bind, evalDist_bind,
            Signing.precomputedSignAttempt_materialized_run_eq_signAttempt
              keyResult hkeyResult hstable largerCache hle leafIndex message randomness]
        _ = evalDist ((simulateQ randomOracle
              (Signing.signAttempt keyResult.1.2 leafIndex message randomness :
                OracleComp HashSpec (Option Signature))).run largerCache >>=
              Signing.signBoundedAttemptsContinuation attempts keyResult.1.2
                leafIndex message) := by
          apply evalDist_bind_congr
          intro result hresult
          cases hoption : result.1 with
          | none =>
              simp only [Signing.precomputedSignBoundedAttemptsContinuation,
                Signing.signBoundedAttemptsContinuation]
              rw [hoption]
              apply ih result.2
              exact hle.trans (CacheReplay.randomOracle_cache_le
                (Signing.signAttempt keyResult.1.2 leafIndex message randomness :
                  OracleComp HashSpec (Option Signature)) largerCache result hresult)
          | some signature =>
              simp only [Signing.precomputedSignBoundedAttemptsContinuation,
                Signing.signBoundedAttemptsContinuation]
              rw [hoption]

theorem Signing.evalDist_precomputedCappedSign_materialized_eq_cappedSign
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (message : Message) :
    evalDist ((simulateQ romImpl
      (Signing.precomputedCappedSign
        (Keygen.materializePrecomputation keyResult.2 keyResult.1.2)
          leafIndex message)).run largerCache) =
      evalDist ((simulateQ romImpl
        (Signing.cappedSign keyResult.1.2 leafIndex message)).run
          largerCache) := by
  rw [Signing.precomputedCappedSign, Signing.cappedSign_eq]
  exact Signing.evalDist_precomputedSignBoundedAttempts_materialized_eq
    Code.signingAttemptLimit keyResult hkeyResult hstable largerCache hle leafIndex message

end Xmss.Generic.CappedExecution

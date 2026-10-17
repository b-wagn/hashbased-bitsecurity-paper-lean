import XmssSecurity.Proof.TargetSum.ExactKeygenQueryCount
import XmssSecurity.Proof.TargetSum.Direct.VerifierBound

/-! Every accepting verification uses exactly 133 hash queries. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum
namespace ExactQueryCount

theorem encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    ExactQueryCount (Concrete.encodingHash parameter leafIndex message randomness :
      OracleComp HashSpec Digest) 1 := tweakableHash _ _ _

theorem leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    ExactQueryCount (Concrete.leafHash parameter leafIndex endpoints :
      OracleComp HashSpec Digest) 1 := tweakableHash _ _ _

theorem recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    ExactQueryCount (Concrete.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)) (TargetSum.verificationWork encoding) := by
  unfold Concrete.recoverEndpoints TargetSum.verificationWork
  apply sequenceFin
  intro chain
  apply chainWalk
  have hdigit := (encoding chain).isLt
  omega

theorem authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : ℕ) (hlevel : level < treeHeight) (current sibling : Digest) :
    ExactQueryCount (Concrete.authenticationNodeHash parameter leafIndex level current sibling :
      OracleComp HashSpec Digest) 1 := by
  unfold Concrete.authenticationNodeHash
  simp only [hlevel, dif_pos]
  split <;> exact tweakableHash _ _ _

theorem authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (levels : ℕ) (hlevels : levels ≤ treeHeight) (leaf : Digest) :
    ExactQueryCount (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest) levels := by
  induction levels with
  | zero => exact .pure leaf
  | succ levels ih =>
      rw [Concrete.authenticationRoot]
      exact (ih (by omega)).bind _ 1 (fun current =>
        authenticationNodeHash parameter leafIndex levels (by omega) current _)

theorem verifyAfterLeaf (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    ExactQueryCount (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool) treeHeight := by
  unfold Concrete.verifyAfterLeaf
  exact (authenticationRoot publicKey.parameter leafIndex signature treeHeight le_rfl leaf).map _

end ExactQueryCount

theorem countHashQueries_lift_exact {computation : OracleComp HashSpec α} {count : ℕ}
    (hexact : ExactQueryCount computation count) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, count)) <$> (liftM computation : OracleComp OracleWorld α) := by
  apply countHashQueries_of_exact
  exact ExactQueryCount.liftComp_predicate hexact IsHashQuery (fun input => by
    change IsHashQuery (.inr input)
    simp [IsHashQuery])

theorem countHashQueries_verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    countHashQueries (Concrete.scheme.verify publicKey leafIndex message signature) = (do
      let digest ← (liftM (Concrete.encodingHash publicKey.parameter leafIndex message
        signature.randomness : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)
      match TargetSum.decodeDigest digest with
      | none => pure (false, 1)
      | some encoding =>
          let endpoints ← liftM (Concrete.recoverEndpoints publicKey.parameter leafIndex
            encoding signature : OracleComp HashSpec (ChainIndex → Digest))
          let leaf ← liftM (Concrete.leafHash publicKey.parameter leafIndex endpoints :
            OracleComp HashSpec Digest)
          let verified ← liftM (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          pure (verified, Direct.verifierQueryBound)) := by
  change countHashQueries (liftM (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool) = _
  rw [Concrete.verify, liftM_bind, countHashQueries_bind,
    countHashQueries_lift_exact (ExactQueryCount.encodingHash _ _ _ _)]
  simp only [bind_map_left]
  apply bind_congr
  intro digest
  cases hdecode : TargetSum.decodeDigest digest with
  | none => simp [countHashQueries_pure]
  | some encoding =>
      have hwork := TargetSum.verificationWork_eq encoding (Direct.decodeDigest_valid hdecode)
      simp only [liftM_bind, countHashQueries_bind,
        countHashQueries_lift_exact (ExactQueryCount.recoverEndpoints _ _ _ _),
        countHashQueries_lift_exact (ExactQueryCount.leafHash _ _ _),
        countHashQueries_lift_exact (ExactQueryCount.verifyAfterLeaf _ _ _ _),
        bind_map_left, bind_assoc, pure_bind, hwork]
      rfl

theorem verify_queryCount_eq_of_accepts (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (cache : QueryCache HashSpec)
    (result : (Bool × ℕ) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries
      (Concrete.scheme.verify publicKey leafIndex message signature))).run cache))
    (haccepts : result.1.1 = true) : result.1.2 = Direct.verifierQueryBound := by
  rw [countHashQueries_verify, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨digest, cache₁⟩, _hdigest, hrest⟩ := hresult
  dsimp only at hrest
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hrest
      subst result
      cases haccepts
  | some encoding =>
      simp only [hdecode, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨endpoints, cache₂⟩, _hendpoints, ⟨⟨leaf, cache₃⟩, _hleaf,
        ⟨⟨verified, cache₄⟩, _hverified, hfinal⟩⟩⟩ := hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst result
      rfl

end XmssSecurity.TargetSum

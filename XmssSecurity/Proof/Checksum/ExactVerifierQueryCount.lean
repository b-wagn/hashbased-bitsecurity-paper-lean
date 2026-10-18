import XmssSecurity.Proof.Generic.ExactKeygenQueryCount
import XmssSecurity.Proof.Generic.Direct.VerifierBound
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-! Every verification uses `1 + work + 1 + 32` hash queries, where `work` is the number of chain
steps of its encoding; an accepting verification therefore uses at least `34`. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum
namespace ExactQueryCount

theorem encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    Generic.ExactQueryCount (Generic.Concrete.encodingHash parameter leafIndex message randomness :
      OracleComp HashSpec Digest) 1 := Generic.ExactQueryCount.tweakableHash _ _ _

theorem leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    Generic.ExactQueryCount (Generic.Concrete.leafHash parameter leafIndex endpoints :
      OracleComp HashSpec Digest) 1 := Generic.ExactQueryCount.tweakableHash _ _ _

theorem recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Generic.Signature) :
    Generic.ExactQueryCount (Generic.Concrete.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)) (Checksum.verificationWork encoding) := by
  unfold Generic.Concrete.recoverEndpoints Checksum.verificationWork
  apply Generic.ExactQueryCount.sequenceFin
  intro chain
  apply Generic.ExactQueryCount.chainWalk
  have hdigit := (encoding chain).isLt
  omega

theorem authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : ℕ) (hlevel : level < treeHeight) (current sibling : Digest) :
    Generic.ExactQueryCount (Generic.Concrete.authenticationNodeHash parameter leafIndex level current sibling :
      OracleComp HashSpec Digest) 1 := by
  unfold Generic.Concrete.authenticationNodeHash
  simp only [hlevel, dif_pos]
  split <;> exact Generic.ExactQueryCount.tweakableHash _ _ _

theorem authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (levels : ℕ) (hlevels : levels ≤ treeHeight) (leaf : Digest) :
    Generic.ExactQueryCount (Generic.Concrete.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest) levels := by
  induction levels with
  | zero => exact .pure leaf
  | succ levels ih =>
      rw [Generic.Concrete.authenticationRoot]
      exact (ih (by omega)).bind _ 1 (fun current =>
        authenticationNodeHash parameter leafIndex levels (by omega) current _)

theorem verifyAfterLeaf (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (leaf : Digest) :
    Generic.ExactQueryCount (Generic.Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool) treeHeight := by
  unfold Generic.Concrete.verifyAfterLeaf
  exact (authenticationRoot publicKey.parameter leafIndex signature treeHeight le_rfl leaf).map _

end ExactQueryCount

theorem countHashQueries_lift_exact {computation : OracleComp HashSpec α} {count : ℕ}
    (hexact : Generic.ExactQueryCount computation count) :
    Generic.countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, count)) <$> (liftM computation : OracleComp OracleWorld α) := by
  apply Generic.countHashQueries_of_exact
  exact Generic.ExactQueryCount.liftComp_predicate hexact Generic.IsHashQuery (fun input => by
    change Generic.IsHashQuery (.inr input)
    simp [Generic.IsHashQuery])

theorem countHashQueries_verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Generic.Signature) :
    Generic.countHashQueries (Generic.Concrete.scheme.verify publicKey leafIndex message signature) = (do
      let digest ← (liftM (Generic.Concrete.encodingHash publicKey.parameter leafIndex message
        signature.randomness : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest)
      match Generic.Code.decodeDigest digest with
      | none => pure (false, 1)
      | some encoding =>
          let endpoints ← liftM (Generic.Concrete.recoverEndpoints publicKey.parameter leafIndex
            encoding signature : OracleComp HashSpec (ChainIndex → Digest))
          let leaf ← liftM (Generic.Concrete.leafHash publicKey.parameter leafIndex endpoints :
            OracleComp HashSpec Digest)
          let verified ← liftM (Generic.Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          pure (verified, 1 + (Checksum.verificationWork encoding + (1 + treeHeight)))) := by
  change Generic.countHashQueries (liftM (Generic.Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) : OracleComp OracleWorld Bool) = _
  rw [Generic.Concrete.verify_eq_decode, liftM_bind, Generic.countHashQueries_bind,
    countHashQueries_lift_exact (ExactQueryCount.encodingHash _ _ _ _)]
  simp only [bind_map_left]
  apply bind_congr
  intro digest
  cases hdecode : Generic.Code.decodeDigest digest with
  | none => simp [Generic.countHashQueries_pure]
  | some encoding =>
      simp only [liftM_bind, Generic.countHashQueries_bind,
        countHashQueries_lift_exact (ExactQueryCount.recoverEndpoints _ _ _ _),
        countHashQueries_lift_exact (ExactQueryCount.leafHash _ _ _),
        countHashQueries_lift_exact (ExactQueryCount.verifyAfterLeaf _ _ _ _),
        bind_map_left, bind_assoc, pure_bind]

theorem verify_queryCount_ge_of_accepts (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Generic.Signature) (cache : QueryCache HashSpec)
    (result : (Bool × ℕ) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ Generic.romImpl (Generic.countHashQueries
      (Generic.Concrete.scheme.verify publicKey leafIndex message signature))).run cache))
    (haccepts : result.1.1 = true) : Generic.Direct.verifierAcceptedMinimum ≤ result.1.2 := by
  rw [countHashQueries_verify, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨digest, cache₁⟩, _hdigest, hrest⟩ := hresult
  dsimp only at hrest
  cases hdecode : Generic.Code.decodeDigest digest with
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
      simp only [Generic.Direct.verifierAcceptedMinimum]
      omega

end XmssSecurity.Checksum

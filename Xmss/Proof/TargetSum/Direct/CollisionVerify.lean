import Xmss.Proof.TargetSum.Direct.CollisionPrehit
import Xmss.Proof.Generic.Direct.VerifierBound
import Xmss.Proof.TargetSum.Direct.VerificationAcceptance
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-!
# Verification touches one encoding input

After its first query, at the forged encoding input, verification only hashes chain values,
the leaf and Merkle nodes, none of them an encoding input (`verifyAfterDigest_noEncoding`). So
verification leaves every other encoding input of the cache as it was
(`run_agree_of_noEncoding`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Direct.Collision

/-- The input is an encoding input. -/
def IsEncodingInput (parameter : PublicParameter) (hashInput : HashInput) : Prop :=
  (encodingInputLeafIndex? parameter hashInput).isSome

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsEncodingInput parameter) :=
  Classical.decPred _

theorem tweakableHashInput_not_encoding (parameter : PublicParameter) (domain : Generic.HashDomain)
    (payload : HashInput) (hdomain : ∀ leafIndex, domain ≠ .encoding leafIndex) :
    ¬ IsEncodingInput parameter (Generic.tweakableHashInput parameter domain payload) := by
  intro h
  obtain ⟨leafIndex, hleafIndex⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨entry, hentry⟩ :=
    exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter _ leafIndex hleafIndex
  exact hdomain leafIndex
    (domain_eq_of_tweakableHashInput_eq parameter hentry).symm

theorem tweakableHash_noEncoding (parameter : PublicParameter) (domain : Generic.HashDomain)
    (payload : HashInput) (hdomain : ∀ leafIndex, domain ≠ .encoding leafIndex) :
    (Generic.Hashing.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      (IsEncodingInput parameter) 0 := by
  have hnot := tweakableHashInput_not_encoding parameter domain payload hdomain
  simp [Generic.Hashing.tweakableHash, Generic.Hashing.oracleHash, hnot]

theorem chainWalk_noEncoding (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Generic.Wots.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP (IsEncodingInput parameter) 0 := by
  induction steps with
  | zero => simp [Generic.Wots.chainWalk]
  | succ steps ih =>
      rw [Generic.Wots.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact tweakableHash_noEncoding _ _ _ fun _ => by simp
      · simp

theorem recoverEndpoints_noEncoding (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Generic.Signature) :
    (Generic.Verify.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP (IsEncodingInput parameter) 0 := by
  unfold Generic.Verify.recoverEndpoints
  have h := Direct.sequenceFin_isQueryBoundP (fun chain => Generic.Verify.recoverChain parameter leafIndex chain
    (encoding chain) (signature.chainValue chain)) (fun _ => 0) (IsEncodingInput parameter)
    fun chain => by
      unfold Generic.Verify.recoverChain
      exact chainWalk_noEncoding _ _ _ _ _ _
  rw [Finset.sum_const_zero] at h
  exact h

theorem authenticationNodeHash_noEncoding (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (current sibling : Digest) :
    (Generic.Verify.authenticationNodeHash parameter leafIndex level current sibling :
      OracleComp HashSpec Digest).IsQueryBoundP (IsEncodingInput parameter) 0 := by
  unfold Generic.Verify.authenticationNodeHash
  split
  · split
    · exact tweakableHash_noEncoding _ _ _ fun _ => by simp
    · exact tweakableHash_noEncoding _ _ _ fun _ => by simp
  · simp

theorem authenticationRoot_noEncoding (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (levels : Nat) (leaf : Digest) :
    (Generic.Verify.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP (IsEncodingInput parameter) 0 := by
  induction levels with
  | zero => simp [Generic.Verify.authenticationRoot]
  | succ levels ih =>
      rw [Generic.Verify.authenticationRoot]
      exact OracleComp.isQueryBoundP_bind (m := 0) ih fun _ _ =>
        authenticationNodeHash_noEncoding _ _ _ _ _

theorem verifyAfterLeaf_noEncoding (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (leaf : Digest) :
    (Generic.Verify.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool).IsQueryBoundP (IsEncodingInput publicKey.parameter) 0 := by
  unfold Generic.Verify.verifyAfterLeaf
  generalize treeHeight = levels
  have hbind := OracleComp.isQueryBoundP_bind (m := 0)
    (authenticationRoot_noEncoding publicKey.parameter leafIndex signature levels leaf)
    (ob := fun root => (pure (decide (root = publicKey.root)) : OracleComp HashSpec Bool))
    (fun _ _ => isQueryBoundP_pure _ _ _)
  rw [Nat.add_zero] at hbind
  exact hbind

theorem verifyAfterDigest_noEncoding (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Generic.Signature) (digest : Digest) :
    (Direct.verifyAfterDigest publicKey leafIndex signature digest).IsQueryBoundP
      (IsEncodingInput publicKey.parameter) 0 := by
  unfold Direct.verifyAfterDigest
  cases Code.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (recoverEndpoints_noEncoding _ _ _ _) fun endpoints _ => ?_
      exact OracleComp.isQueryBoundP_bind (m := 0)
        (tweakableHash_noEncoding _ _ _ fun _ => by simp) fun leaf _ =>
          verifyAfterLeaf_noEncoding _ _ _ _

/-- A computation without encoding queries leaves every encoding input of the cache as it was. -/
theorem run_agree_of_noEncoding {β : Type} (parameter : PublicParameter)
    (computation : OracleComp HashSpec β)
    (hbound : computation.IsQueryBoundP (IsEncodingInput parameter) 0)
    (cache : QueryCache HashSpec) :
    ∀ result ∈ support ((simulateQ randomOracle computation).run cache),
      AgreeOnEncoding parameter cache result.2 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      exact fun _ _ => rfl
  | query_bind query next ih =>
      intro result hresult
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hnot : ¬ IsEncodingInput parameter query := by simpa using hbound.1
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨middle, hmiddle, hrest⟩ := hresult
      have hnext := hbound.2 middle.1
      rw [if_neg hnot] at hnext
      have hagreeMiddle : AgreeOnEncoding parameter cache middle.2 := by
        intro leafIndex entry
        have hne : input parameter leafIndex entry ≠ query := by
          intro heq
          apply hnot
          rw [← heq]
          simp [IsEncodingInput]
        replace hmiddle : middle ∈ support ((randomOracle (spec := HashSpec) query).run cache) := by
          simpa [simulateQ_query] using hmiddle
        cases hcached : cache query with
        | some found =>
            rw [randomOracle, QueryImpl.withCaching_run_some _ hcached, support_pure,
              Set.mem_singleton_iff] at hmiddle
            rw [hmiddle]
        | none =>
            rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, support_map] at hmiddle
            obtain ⟨sampled, -, hsampled⟩ := hmiddle
            rw [← hsampled]
            exact QueryCache.cacheQuery_of_ne _ _ hne
      have hfinal := ih middle.1 hnext middle.2 result hrest
      exact fun leafIndex entry => (hfinal leafIndex entry).trans (hagreeMiddle leafIndex entry)

end Xmss.TargetSum.Direct.Collision

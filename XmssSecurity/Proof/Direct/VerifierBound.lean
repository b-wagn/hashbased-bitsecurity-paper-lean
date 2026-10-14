import XmssSecurity.Proof.Direct.Basic
import XmssSecurity.Proof.ConsistentQueryBound
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The verifier's worst-case hash queries

One verification makes at most `verifierQueryBound = 1 + 99 + 1 + 32 = 133` hash queries on
every branch, whatever the oracle answers: the encoding hash; if the digest decodes, the
`verificationWork x = 99` chain steps of a valid encoding, the leaf hash and the `32` Merkle levels.
The bound is stated syntactically (`IsQueryBoundP`) and, for every starting cache, as a
`HashQueryBound` of the lifted verifier in the random-oracle world.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Direct

set_option backward.isDefEq.respectTransparency false

/-! ## The building blocks, in `OracleComp HashSpec` -/

theorem tweakableHash_isQueryBoundP (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      (fun _ => True) 1 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash]

theorem chainWalk_isQueryBoundP (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP (fun _ => True) steps := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih ?_
      intro previous _
      split
      · exact tweakableHash_isQueryBoundP _ _ _
      · simp

theorem sequenceFin_isQueryBoundP {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (bound : Fin n → Nat)
    (p : HashInput → Prop) [DecidablePred p]
    (hbound : ∀ index, (computation index).IsQueryBoundP p (bound index)) :
    (Concrete.sequenceFin computation).IsQueryBoundP p (∑ index, bound index) := by
  induction n with
  | zero => simp [Concrete.sequenceFin]
  | succ n ih =>
      rw [Concrete.sequenceFin, Fin.sum_univ_succ]
      refine OracleComp.isQueryBoundP_bind (hbound 0) ?_
      intro head _
      have htail := OracleComp.isQueryBoundP_bind (m := 0)
        (ih (fun index => computation index.succ) (fun index => bound index.succ)
          (fun index => hbound index.succ))
        (ob := fun tail => (pure (Fin.cases head tail) : OracleComp HashSpec (Fin (n + 1) → α)))
        (fun _ _ => by simp)
      simpa using htail

theorem recoverEndpoints_isQueryBoundP (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    (Concrete.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP (fun _ => True)
        (TargetSum.verificationWork encoding) := by
  unfold Concrete.recoverEndpoints TargetSum.verificationWork
  exact sequenceFin_isQueryBoundP _ _ _ fun chain =>
    chainWalk_isQueryBoundP _ _ _ _ _ _

theorem authenticationNodeHash_isQueryBoundP (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (current sibling : Digest) :
    (Concrete.authenticationNodeHash parameter leafIndex level current sibling :
      OracleComp HashSpec Digest).IsQueryBoundP (fun _ => True) 1 := by
  unfold Concrete.authenticationNodeHash
  split
  · split
    · exact tweakableHash_isQueryBoundP _ _ _
    · exact tweakableHash_isQueryBoundP _ _ _
  · simp

theorem authenticationRoot_isQueryBoundP (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (levels : Nat) (leaf : Digest) :
    (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP (fun _ => True) levels := by
  induction levels with
  | zero => simp [Concrete.authenticationRoot]
  | succ levels ih =>
      rw [Concrete.authenticationRoot]
      exact OracleComp.isQueryBoundP_bind ih fun _ _ =>
        authenticationNodeHash_isQueryBoundP _ _ _ _ _

theorem verifyAfterLeaf_isQueryBoundP (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) treeHeight := by
  unfold Concrete.verifyAfterLeaf
  generalize treeHeight = levels
  have hroot := authenticationRoot_isQueryBoundP publicKey.parameter leafIndex signature
    levels leaf
  have hbind := OracleComp.isQueryBoundP_bind (m := 0) hroot
    (ob := fun root => (pure (decide (root = publicKey.root)) : OracleComp HashSpec Bool))
    (fun _ _ => isQueryBoundP_pure _ _ _)
  rw [Nat.add_zero] at hbind
  exact hbind

theorem decodeDigest_valid {digest : Digest} {encoding : Encoding}
    (h : TargetSum.decodeDigest digest = some encoding) : TargetSum.Valid encoding := by
  exact (TargetSum.decodeDigest_eq_some_iff.mp h).2

/-! ## The verifier -/

/-- One verification makes at most `verifierQueryBound = 133` hash queries on every branch. -/
theorem verify_isQueryBoundP (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.verify publicKey leafIndex message signature :
      OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) verifierQueryBound := by
  unfold Concrete.verify
  have hsplit : verifierQueryBound = 1 + (verificationChainHashes + (1 + treeHeight)) := by
    unfold verifierQueryBound; omega
  rw [hsplit]
  refine OracleComp.isQueryBoundP_bind (tweakableHash_isQueryBoundP _ _ _) ?_
  intro digest _
  cases hdecode : TargetSum.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only
      have hwork := TargetSum.verificationWork_eq encoding (decodeDigest_valid hdecode)
      refine OracleComp.isQueryBoundP_bind ?_ fun endpoints _ =>
        OracleComp.isQueryBoundP_bind (tweakableHash_isQueryBoundP _ _ _) fun leaf _ =>
          verifyAfterLeaf_isQueryBoundP _ _ _ _
      rw [← hwork]
      exact recoverEndpoints_isQueryBoundP _ _ _ _

/-! ## The lifted verifier -/

/-- The scheme's verifier makes at most `verifierQueryBound` hash queries on every branch. -/
theorem scheme_verify_isQueryBoundP (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.scheme.verify publicKey leafIndex message signature).IsQueryBoundP
      (fun input : OracleWorld.Domain => input matches .inr _) verifierQueryBound := by
  change (liftComp (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True)
    (fun input => iff_of_true trivial rfl)
    (verify_isQueryBoundP publicKey leafIndex message signature)

/-- The scheme's verifier makes at most `verifierQueryBound` hash queries on every branch,
counting every query. -/
theorem scheme_verify_isQueryBoundP_true (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.scheme.verify publicKey leafIndex message signature).IsQueryBoundP
      (fun _ => True) verifierQueryBound := by
  change (liftComp (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ => True)
    (fun input => by simp) (verify_isQueryBoundP publicKey leafIndex message signature)

/-! ## From the syntactic to the semantic bound -/

/-- A syntactic bound on the hash queries bounds the counted hash queries under the consistent
random oracle, from every starting cache. -/
theorem hashQueryBound_of_isQueryBoundP {α : Type} (computation : OracleComp OracleWorld α)
    (n : Nat)
    (hbound : computation.IsQueryBoundP
      (fun input : OracleWorld.Domain => input matches .inr _) n)
    (cache : QueryCache HashSpec) : HashQueryBound computation cache n := by
  induction computation using OracleComp.inductionOn generalizing n cache with
  | pure value =>
      intro result hresult
      simp [countHashQueries_pure] at hresult
      subst hresult
      simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      intro result hresult
      rw [countHashQueries_query_bind] at hresult
      simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
        StateT.run_pure, support_map, support_bind, Set.mem_image, Set.mem_iUnion,
        support_pure, Set.mem_singleton_iff] at hresult
      obtain ⟨⟨value, count⟩, ⟨⟨answer, cache₁⟩, _, ⟨inner, cache₂⟩, hinner, hfinal⟩, rfl⟩ :=
        hresult
      simp only [Prod.mk.injEq] at hfinal
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hfinal
      have hrest := ih answer _ (hbound.2 answer) cache₁ inner
        (by simp only [StateT.run'_eq, support_map, Set.mem_image]; exact ⟨_, hinner, rfl⟩)
      rcases input with input | input <;> simp_all; omega

/-- For every starting cache, the scheme's verifier makes at most `verifierQueryBound` hash
queries under the consistent random oracle. -/
theorem scheme_verify_hashQueryBound (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (cache : QueryCache HashSpec) :
    HashQueryBound (Concrete.scheme.verify publicKey leafIndex message signature) cache
      verifierQueryBound :=
  hashQueryBound_of_isQueryBoundP _ _
    (scheme_verify_isQueryBoundP publicKey leafIndex message signature) cache

end XmssSecurity.Direct

import XmssSecurity.Proof.Checksum.Direct.Basic
import XmssSecurity.Proof.Checksum.ConsistentQueryBound
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# The verifier's worst-case hash queries

One verification makes at most `verifierQueryBound = 1 + 322 + 1 + 32 = 356` hash queries on
every branch, whatever the oracle answers: the encoding hash; if the digest decodes, the
`verificationWork x ≤ 322` chain steps of an encoding, the leaf hash and the `32` Merkle levels.
The bound is stated syntactically (`IsQueryBoundP`) and, for every starting cache, as a
`HashQueryBound` of the lifted verifier in the random-oracle world.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Checksum.Direct

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
        (Checksum.verificationWork encoding) := by
  unfold Concrete.recoverEndpoints Checksum.verificationWork
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
    (h : Checksum.decodeDigest digest = some encoding) : Checksum.Valid encoding := by
  exact Checksum.decodeDigest_valid h

/-! ## The verifier -/

/-- One verification makes at most `verifierQueryBound = 356` hash queries on every branch. -/
theorem verify_isQueryBoundP (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.verify publicKey leafIndex message signature :
      OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) verifierQueryBound := by
  simp only [Concrete.verify_eq_decode]
  have hsplit : verifierQueryBound = 1 + (verificationChainHashes + (1 + treeHeight)) := by
    unfold verifierQueryBound; omega
  rw [hsplit]
  refine OracleComp.isQueryBoundP_bind (tweakableHash_isQueryBoundP _ _ _) ?_
  intro digest _
  cases hdecode : Checksum.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only
      refine OracleComp.isQueryBoundP_bind ?_ fun endpoints _ =>
        OracleComp.isQueryBoundP_bind (tweakableHash_isQueryBoundP _ _ _) fun leaf _ =>
          verifyAfterLeaf_isQueryBoundP _ _ _ _
      exact (recoverEndpoints_isQueryBoundP _ _ _ _).mono (Checksum.verificationWork_le encoding)

/-! ## The lifted verifier -/

/-! ## From the syntactic to the semantic bound -/

end XmssSecurity.Checksum.Direct

import Xmss.Proof.Generic.ExactQueryCount
import Xmss.Proof.Generic.CacheReplayEval
import Xmss.Proof.Generic.DetailedExecution
import Xmss.Proof.Generic.CappedExecution.EncodingQueryBound
import VCVio.OracleComp.QueryTracking.QueryBound
import Xmss.Proof.Generic.IdealStatement
import Xmss.Proof.Generic.StatementLemmas
import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec
open scoped BigOperators

namespace Xmss.Generic

variable [Code]

def treeHashQueryCount : Nat → Nat
  | 0 => Code.numChains * (chainLength - 1) + 1
  | levels + 1 => 2 * treeHashQueryCount levels + 1

namespace ExactQueryCount

theorem oneTimePublicKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Wots.oneTimePublicKey (m := OracleComp HashSpec) parameter secret leafIndex)
      (Code.numChains * (chainLength - 1)) := by
  unfold Wots.oneTimePublicKey
  have hexact := sequenceFin
    (fun chain : ChainIndex =>
      Wots.chainWalk (m := OracleComp HashSpec) parameter leafIndex chain 0
        (chainLength - 1) (secret leafIndex chain))
    (fun _ : ChainIndex => chainLength - 1)
    (fun chain => chainWalk parameter leafIndex chain 0 (chainLength - 1)
      (secret leafIndex chain) (by omega))
  simpa using hexact

theorem leafAt (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) :
    ExactQueryCount
      (Merkle.leafAt (m := OracleComp HashSpec) parameter secret leafIndex)
      (Code.numChains * (chainLength - 1) + 1) := by
  unfold Merkle.leafAt
  exact (oneTimePublicKey parameter secret leafIndex).bind
    (fun endpoints => Hashing.leafHash parameter leafIndex endpoints) 1
    (fun endpoints => tweakableHash parameter (.leaf leafIndex)
      (Hashing.leafPayload endpoints))

theorem treeNode (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) :
    ExactQueryCount
      (Merkle.treeNode (m := OracleComp HashSpec) parameter secret levels node)
      (treeHashQueryCount levels) := by
  induction levels generalizing node with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      exact leafAt parameter secret node
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Merkle.treeNode_succ_eq]
      have hleft := ih (Merkle.childNode node false) (Nat.le_of_succ_le hlevels)
      have hright := ih (Merkle.childNode node true) (Nat.le_of_succ_le hlevels)
      have hcontinuation (left : Digest) :
          ExactQueryCount (do
            let right ← Merkle.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Merkle.childNode node true)
            Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right)
            (treeHashQueryCount levels + 1) :=
        hright.bind
          (fun right => Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right) 1
          (fun right => tweakableHash parameter (.merkle ⟨levels, hlevel⟩ node)
            (Hashing.nodePayload left right))
      simpa [hlevel, treeHashQueryCount, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.two_mul] using
        hleft.bind
          (fun left => do
            let right ← Merkle.treeNode (m := OracleComp HashSpec) parameter secret levels
              (Merkle.childNode node true)
            Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right)
          (treeHashQueryCount levels + 1) hcontinuation

theorem rootTree (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) :
    ExactQueryCount
      (Merkle.treeNode (m := OracleComp HashSpec) parameter secret treeHeight
        Merkle.rootNode)
      (treeHashQueryCount treeHeight) :=
  treeNode parameter secret treeHeight Merkle.rootNode le_rfl

end ExactQueryCount

theorem treeHashQueryCount_base_le (levels : Nat) :
    Code.numChains * (chainLength - 1) + 1 ≤ treeHashQueryCount levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simp only [treeHashQueryCount]
      omega

def IsHashQuery : OracleWorld.Domain → Prop := fun input => input matches .inr _

instance : DecidablePred IsHashQuery := by
  intro input
  cases input <;> unfold IsHashQuery <;> exact inferInstance

namespace ExactQueryCount.ExactPredicateQueryCount

omit [Code] in
theorem liftProbComp_hashCount_zero (computation : ProbComp α) :
    ExactPredicateQueryCount IsHashQuery
      (liftM computation : OracleComp OracleWorld α) 0 := by
  apply ExactQueryCount.ExactPredicateQueryCount.of_isQueryBoundP_zero
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun _ : unifSpec.Domain => False) (q := IsHashQuery)
    (fun input => by simp [IsHashQuery])
    (OracleComp.isQueryBoundP_false computation 0)

end ExactQueryCount.ExactPredicateQueryCount

omit [Code] in
theorem countHashQueries_of_exact {α : Type} {computation : OracleComp OracleWorld α} {count : Nat}
    (hexact : ExactPredicateQueryCount IsHashQuery computation count) :
    countHashQueries computation = (fun value => (value, count)) <$> computation := by
  induction hexact with
  | pure value => simp only [countHashQueries_pure, map_pure]
  | query input next count hnext ih =>
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      cases input <;> simp [IsHashQuery, Nat.add_comm]

namespace CappedExecution

end CappedExecution

end Xmss.Generic

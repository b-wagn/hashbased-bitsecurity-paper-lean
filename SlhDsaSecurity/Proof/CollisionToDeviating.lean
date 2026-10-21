import SlhDsaSecurity.Proof.CanonicalTarget
import SlhDsaSecurity.Proof.Extraction.BinaryPath

/-!
# Path collisions are deviating canonical-graph queries

Every authentication-path collision extracted from a forgery — Merkle in
`Extraction.Merkle`, FORS in `Extraction.Fors`, and the layer collisions of
`Extraction.Hypertree` — has the shape `BinaryPath.Collision`: at some height the supplied
child pair differs from the canonical one, yet hashing it under that node's address
reproduces the canonical parent value.

`StructuralTerm.DeviatingCollision` has exactly that shape in canonical-graph terms: a query
whose parsed child values deviate from the honest cells at some parent, whose cached answer
truncates to the parent's honest cell. This file supplies the byte-level bridge between the
two: a binary structural node has exactly two children, and the canonical graph's
`childBytes` encoding of a two-child node is literally `BinaryPath.pairBytes`.

With this, mapping a path collision to a deviating query is a matter of naming the parent
node and the candidate cells; the byte inputs already agree on the nose.
-/

namespace SlhDsaSecurity.CollisionToDeviating

open CanonicalGraph

/-- The canonical graph's child encoding of a two-child node is the binary-path pair
encoding. -/
theorem childBytes_pair (cells : Cells) (left right : Node) :
    childBytes cells [left, right] =
      Extraction.BinaryPath.pairBytes (cells left, cells right) := by
  simp [childBytes, Extraction.BinaryPath.pairBytes]

/-- A tree node's canonical query input is the tweakable input on its two children's pair
bytes, under its own address. -/
theorem canonicalInput_tree (publicSeed : Digest) (cells : Cells)
    (location : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) :
    canonicalInput publicSeed cells (.tree location height index) =
      Hashing.tweakableInput publicSeed
        (StructuralNode.tree location height index).address
        (Extraction.BinaryPath.pairBytes
          (cells (.structural (merkleChild location height index 0)),
            cells (.structural (merkleChild location height index 1)))) := by
  unfold canonicalInput
  exact congrArg
    (Hashing.tweakableInput publicSeed
      (StructuralNode.tree location height index).address)
    (childBytes_pair cells _ _)

/-- The two children of a tree node, as a pair, determine candidate cells agreeing with the
supplied pair. Deviation of the pair is deviation of the cells at a child. -/
theorem exists_deviating_child (cells : Cells) (left right : Node)
    (actualLeft actualRight : Digest)
    (hne : (actualLeft, actualRight) ≠ (cells left, cells right))
    (hdistinct : left ≠ right) :
    ∃ candidates : Cells,
      candidates left = actualLeft ∧ candidates right = actualRight ∧
        ∃ child ∈ [left, right], candidates child ≠ cells child := by
  classical
  refine ⟨fun node => if node = left then actualLeft else
    if node = right then actualRight else cells node, ?_, ?_, ?_⟩
  · simp
  · simp [hdistinct.symm]
  · by_cases hleft : actualLeft = cells left
    · refine ⟨right, by simp, ?_⟩
      have hright : actualRight ≠ cells right := by
        intro hright
        exact hne (by rw [hleft, hright])
      simpa [hdistinct.symm] using hright
    · exact ⟨left, by simp, by simpa using hleft⟩

end SlhDsaSecurity.CollisionToDeviating

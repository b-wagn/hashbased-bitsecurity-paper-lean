import SlhDsaSecurity.Proof.CanonicalGraph.Children

/-!
# Why a sensitive query costs one unit and not several

The input half charges one event: the adversary queries the canonical input of a node one of
whose children's cells the signatures so far do not make available. A canonical input is
`PK.seed ‖ ADRS ‖ (its children's cells)`, so the address says which node, and the query
matches only if its payload reproduces that node's children exactly. If a node had *two*
children the signatures withhold, the adversary would have to match both — harmless — but if a
node had two children of which only one is withheld in some runs and the other in others, the
rate would be a union over the possibilities rather than a single `2 ^ -128`.

The budget allows exactly two units of `2 ^ -129` for this event, so the rate has to be
`2 ^ -128` on the nose. That is a fact about the shape of the graph, proved here and
independent of what "available" ends up meaning: **every node either has only children whose
cells no signature can withhold, or has exactly one child.**

The cells the charge has to protect are the secret seed, the WOTS chain values *below* the
endpoint, and the FORS secrets. A chain's endpoint is excluded, and the reason is not that no
run could fail to hold it — a WOTS key nobody ever signed with reveals none of its chain — but
that the charge never needs it: what a hypertree fault leaves in the adversary's hands is a
chain value strictly below the revealed digit, hence strictly below `w - 1`, and the queries
that could have produced it are at lower positions still. Excluding the endpoint is what keeps
`wotsPk`, with its `chains` children, on the harmless side. Merkle and FORS tree nodes collect
tree cells and `forsRoots` collects tree roots, which are public outright.
-/

namespace SlhDsaSecurity.CanonicalGraph

/-- The cells the input half does not have to protect: everything except the secret seed, a
WOTS chain value strictly below the endpoint, and a FORS secret. -/
def AlwaysAvailable : Node → Prop
  | .secretSeed => False
  | .structural (.wotsPrf _ _) => False
  | .structural (.wotsHash _ _ step) => step.val = w - 2
  | .structural (.forsPrf _ _) => False
  | .structural (.wotsPk _) => True
  | .structural (.tree _ _ _) => True
  | .structural (.forsTree _ _ _) => True
  | .structural (.forsRoots _) => True

/-- A Merkle child is a subtree node or a WOTS public key, never a protected cell. -/
theorem alwaysAvailable_merkleChild (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) (side : Fin 2) :
    AlwaysAvailable (.structural (merkleChild tree height index side)) := by
  rw [merkleChild, merkleNode]
  split <;> exact True.intro

/-- **Every node has only unprotected children, or exactly one child.** -/
theorem children_alwaysAvailable_or_singleton (parent : StructuralNode) :
    (∀ child ∈ parent.children, AlwaysAvailable child) ∨
      ∃ child : Node, parent.children = [child] := by
  cases parent with
  | wotsPrf key chain => exact Or.inr ⟨.secretSeed, rfl⟩
  | wotsHash key chain step =>
    refine Or.inr ?_
    rw [StructuralNode.children]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | wotsPk key =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children, List.mem_ofFn] at hchild
    obtain ⟨chain, rfl⟩ := hchild
    exact rfl
  | tree location height index =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children] at hchild
    rcases List.mem_cons.mp hchild with rfl | hchild
    · exact alwaysAvailable_merkleChild location height index 0
    · rw [List.mem_singleton] at hchild
      subst hchild
      exact alwaysAvailable_merkleChild location height index 1
  | forsPrf key index => exact Or.inr ⟨.secretSeed, rfl⟩
  | forsTree key height index =>
    rw [StructuralNode.children]
    split
    · exact Or.inr ⟨_, rfl⟩
    · refine Or.inl fun child hchild => ?_
      rcases List.mem_cons.mp hchild with rfl | hchild
      · exact True.intro
      · rw [List.mem_singleton] at hchild
        subst hchild
        exact True.intro
  | forsRoots key =>
    refine Or.inl fun child hchild => ?_
    rw [StructuralNode.children, List.mem_ofFn] at hchild
    obtain ⟨tree, rfl⟩ := hchild
    exact True.intro

end SlhDsaSecurity.CanonicalGraph

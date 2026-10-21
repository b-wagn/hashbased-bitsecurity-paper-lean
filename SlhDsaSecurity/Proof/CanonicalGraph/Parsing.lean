import SlhDsaSecurity.Proof.CanonicalGraph.Input

/-!
An input-only parser for the canonical graph. The parser uses only the public seed and
query bytes. Its candidate table is a witness reconstructed from those bytes, not the
secret table. Values at coordinates outside the parsed parent's children are irrelevant.
The parser is noncomputable because efficiency is immaterial for the query-count reduction.
-/

namespace SlhDsaSecurity.CanonicalGraph

structure ParsedInput where
  parent : StructuralNode
  candidates : Cells

def HasParse (publicSeed : Digest) (input : Bytes) : Prop :=
  ∃ parsed : ParsedInput, canonicalInput publicSeed parsed.candidates parsed.parent = input

noncomputable def parseInput (publicSeed : Digest) (input : Bytes) : Option ParsedInput := by
  classical
  exact if h : HasParse publicSeed input then some h.choose else none

theorem parseInput_sound {publicSeed : Digest} {input : Bytes} {parsed : ParsedInput}
    (hparse : parseInput publicSeed input = some parsed) :
    canonicalInput publicSeed parsed.candidates parsed.parent = input := by
  classical
  unfold parseInput at hparse
  split at hparse
  · rename_i hexists
    have heq := Option.some.inj hparse
    subst parsed
    exact hexists.choose_spec
  · contradiction

theorem parseInput_none_iff (publicSeed : Digest) (input : Bytes) :
    parseInput publicSeed input = none ↔ ¬ HasParse publicSeed input := by
  classical
  simp [parseInput]

theorem parseInput_canonical (publicSeed : Digest) (cells : Cells) (parent : StructuralNode) :
    ∃ parsed, parseInput publicSeed (canonicalInput publicSeed cells parent) = some parsed ∧
      parsed.parent = parent ∧
        ∀ child ∈ parent.children, parsed.candidates child = cells child := by
  classical
  have hexists : HasParse publicSeed (canonicalInput publicSeed cells parent) :=
    ⟨⟨parent, cells⟩, rfl⟩
  have hparse : parseInput publicSeed (canonicalInput publicSeed cells parent) =
      some hexists.choose := by simp [parseInput, hexists]
  have heq := canonicalInput_eq_iff.mp (parseInput_sound hparse)
  refine ⟨hexists.choose, hparse, heq.2.1, ?_⟩
  simpa only [heq.2.1] using heq.2.2

theorem parseInput_canonical_parent {publicSeed : Digest} {cells : Cells}
    {parent : StructuralNode} {parsed : ParsedInput}
    (hparse : parseInput publicSeed (canonicalInput publicSeed cells parent) = some parsed) :
    parsed.parent = parent :=
  canonicalInput_parent (parseInput_sound hparse)

theorem parseInput_canonical_candidate {publicSeed : Digest} {cells : Cells}
    {parent : StructuralNode} {parsed : ParsedInput}
    (hparse : parseInput publicSeed (canonicalInput publicSeed cells parent) = some parsed)
    {child : Node} (hchild : child ∈ parent.children) :
    parsed.candidates child = cells child := by
  obtain ⟨_, hparent, hvalues⟩ := canonicalInput_eq_iff.mp (parseInput_sound hparse)
  exact hvalues child (hparent ▸ hchild)

/-- The first hidden child is selected using only parsed public bytes and the reveal set. -/
def ParsedInput.firstHiddenChild (parsed : ParsedInput) (revealed : Finset Node) : Option Node :=
  parsed.parent.children.find? fun child => decide (child ∉ revealed)

theorem ParsedInput.firstHiddenChild_some {parsed : ParsedInput} {revealed : Finset Node}
    {child : Node} (hchild : parsed.firstHiddenChild revealed = some child) :
    child ∈ parsed.parent.children ∧ child ∉ revealed := by
  change parsed.parent.children.find? (fun node => decide (node ∉ revealed)) = some child at hchild
  exact ⟨List.mem_of_find?_eq_some hchild, by simpa using (List.find?_some hchild)⟩

theorem ParsedInput.firstHiddenChild_none_iff (parsed : ParsedInput) (revealed : Finset Node) :
    parsed.firstHiddenChild revealed = none ↔ ∀ child ∈ parsed.parent.children, child ∈ revealed := by
  simp [firstHiddenChild, List.find?_eq_none]

/-- The blind probe's coordinate and candidate depend on no hidden table values. -/
noncomputable def blindProbe (publicSeed : Digest) (input : Bytes)
    (revealed : Finset Node) : Option (Node × Digest) := do
  let parsed ← parseInput publicSeed input
  let child ← parsed.firstHiddenChild revealed
  return (child, parsed.candidates child)

theorem blindProbe_of_parse {publicSeed : Digest} {input : Bytes} {revealed : Finset Node}
    {parsed : ParsedInput} {child : Node}
    (hparse : parseInput publicSeed input = some parsed)
    (hchild : parsed.firstHiddenChild revealed = some child) :
    blindProbe publicSeed input revealed = some (child, parsed.candidates child) := by
  simp [blindProbe, hparse, hchild]

/-- Any canonical query that contains a hidden child makes the blind probe hit that child. -/
theorem blindProbe_canonical (publicSeed : Digest) (cells : Cells) (parent : StructuralNode)
    (revealed : Finset Node) (hhidden : ∃ child ∈ parent.children, child ∉ revealed) :
    ∃ child ∈ parent.children, child ∉ revealed ∧
      blindProbe publicSeed (canonicalInput publicSeed cells parent) revealed =
        some (child, cells child) := by
  obtain ⟨parsed, hparse, hparent, hvalues⟩ := parseInput_canonical publicSeed cells parent
  cases hchild : parsed.firstHiddenChild revealed with
  | none =>
      have hall := (parsed.firstHiddenChild_none_iff revealed).mp hchild
      obtain ⟨child, hmem, hnot⟩ := hhidden
      exact False.elim (hnot (hall child (hparent ▸ hmem)))
  | some child =>
      obtain ⟨hmem, hnot⟩ := ParsedInput.firstHiddenChild_some hchild
      have hmem' : child ∈ parent.children := hparent ▸ hmem
      refine ⟨child, hmem', hnot, ?_⟩
      rw [blindProbe_of_parse hparse hchild, hvalues child hmem']

end SlhDsaSecurity.CanonicalGraph

import SlhDsaSecurity.Proof.SensitiveQuery
import SlhDsaSecurity.Proof.SensitiveShape
import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.Extraction.HypertreeChain
import SlhDsaSecurity.Proof.Extraction.Fors
import SlhDsaSecurity.Proof.CacheReplay

/-!
# The canonical graph as a stakes structure

`SensitiveQuery` charges a query at a node one of whose children's cells is unavailable, against
an abstract `Stakes` structure: a node type, the canonical input as a function of the one cell at
stake, a way to read the node back off a candidate input, and the cell that child contributes.
This file builds that structure for the canonical graph, and discharges the closure condition
the charge is worthless without.

Three choices make it fit.

* **The node type carries its own singleton witness.** `Stakes` needs `inputOf` to take exactly
  one cell, and a bare `StructuralNode` with two children has no single cell at stake. So the
  node is a structural node bundled with a proof that it has exactly one child —
  `CanonicalGraph.singleton_children_of_sensitive` supplies that for every sensitive node, and
  bundling it is where the single-unavailable-child hypothesis is spent rather than assumed.
* **`locate` needs no parser.** `CanonicalGraph.canonicalInput_eq_iff` already says the address
  determines the node and the payload determines the children's cells, so reading the node back
  is a choice from the (unique) preimage rather than a byte-level parse.
* **The closure graph is a different graph.** A run computes a node's cell from *all* of that
  node's children, sensitive or not, so `Graph` is built on bare `StructuralNode` while `Stakes`
  is built on the bundled one. `SensitiveQuery` keeps the two apart for exactly this reason.

The revealed digit is instantiated concretely. Each WOTS key of the hypertree signs exactly one
message and that message is a function of the key and the seeds alone — the honest node one
layer down, or at the bottom layer the honest FORS public key at that leaf — so the digit each
key discloses is fixed before the adversary runs. Nothing about it waits on the signing log,
which is what lets the WOTS clause be read off the walk. The FORS side is the opposite and stays
a function of the state.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.GraphStakes

open CanonicalGraph SensitiveQuery

/-! ## The node a sensitive query names

`SensitiveQuery.Stakes` wants a node type on which `stake` is total and `inputOf` takes exactly
one cell. A bare `StructuralNode` is neither: a node with two children has no single cell at
stake. So the node type carries its own witness of having exactly one child — which
`CanonicalGraph.singleton_children_of_sensitive` supplies for every sensitive node, and which is
where the whole single-unavailable-child hypothesis is spent. -/

/-- A structural node together with the single child a sensitive node has. -/
structure SensitiveNode where
  /-- The node itself. -/
  parent : StructuralNode
  /-- Its only child. -/
  child : Node
  /-- Having only that child. -/
  children_eq : parent.children = [child]

theorem SensitiveNode.ext {left right : SensitiveNode} (hparent : left.parent = right.parent) :
    left = right := by
  obtain ⟨leftParent, leftChild, leftEq⟩ := left
  obtain ⟨rightParent, rightChild, rightEq⟩ := right
  cases hparent
  cases List.head_eq_of_cons_eq (leftEq.symm.trans rightEq)
  rfl

variable (publicSeed : Digest)

/-- The canonical input of a sensitive node, as a function of the one cell at stake. -/
def inputOf (node : SensitiveNode) (cell : Cell) : Bytes :=
  Hashing.tweakableInput publicSeed node.parent.address (bytesBE n cell)

/-- It is the node's canonical input, with the staked cell taking that value. -/
theorem inputOf_eq_canonicalInput (node : SensitiveNode) (cells : Cells) :
    inputOf publicSeed node (cells node.child) =
      canonicalInput publicSeed cells node.parent := by
  rw [inputOf, canonicalInput, node.children_eq, CollisionToDeviating.childBytes_single]

/-- **A candidate input determines both the node and the cell**: the address is in the clear
and so is the payload. -/
theorem inputOf_inj {left right : SensitiveNode} {leftCell rightCell : Cell}
    (hinput : inputOf publicSeed left leftCell = inputOf publicSeed right rightCell) :
    left = right ∧ leftCell = rightCell := by
  obtain ⟨-, haddress, hpayload⟩ := Hashing.tweakableInput_injective hinput
  exact ⟨SensitiveNode.ext (StructuralNode.address_injective haddress),
    bytesBE_injective n hpayload⟩

open scoped Classical in
/-- The node a candidate input's address names, if any. -/
noncomputable def locate (input : Bytes) : Option SensitiveNode :=
  if hsome : ∃ node : SensitiveNode, ∃ cell : Cell, inputOf publicSeed node cell = input
    then some hsome.choose else none

theorem locate_inputOf (node : SensitiveNode) (cell : Cell) :
    locate publicSeed (inputOf publicSeed node cell) = some node := by
  classical
  have hsome : ∃ other : SensitiveNode, ∃ value : Cell,
      inputOf publicSeed other value = inputOf publicSeed node cell := ⟨node, cell, rfl⟩
  rw [locate, dif_pos hsome]
  obtain ⟨value, hvalue⟩ := hsome.choose_spec
  exact congrArg some (inputOf_inj publicSeed hvalue).1

/-- **The canonical graph, as the charge's stakes structure.** -/
noncomputable def stakes : Stakes SensitiveNode Node where
  inputOf := inputOf publicSeed
  locate := locate publicSeed
  stake := SensitiveNode.child
  locate_inputOf := locate_inputOf publicSeed
  inputOf_injective := fun _ _ _ hinput => (inputOf_inj publicSeed hinput).2

/-! ## Availability, and its closure

The graph the closure condition speaks about is the whole structure, not only its sensitive
part: a run computes a node's cell from *all* of that node's children, sensitive or not. So the
two structures have different node types, which is why `SensitiveQuery` keeps `Stakes` and
`Graph` apart. -/

/-- The structure availability has to be closed under. -/
def graph : Graph StructuralNode Node where
  cellOf := fun parent => .structural parent
  children := fun parent index => index ∈ parent.children

variable {State : Type} (revealed : WotsKey → Fin chains → Nat)
    (signedAt : State → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))

/-- The cells the signatures issued by a given state do not make available. -/
def unavailableAt (state : State) (index : Node) : Prop :=
  ¬ Available revealed (signedAt state) index

/-- **Availability is closed under the structure.** -/
theorem closed : Closed graph (unavailableAt revealed signedAt) := by
  classical
  intro state parent hchildren hbad
  exact hbad (available_of_children_available revealed (signedAt state)
    fun child hchild => not_not.mp (hchildren child hchild))

/-- **Nothing a run can compute from the available cells is unavailable.** The instance of
`SensitiveQuery.not_unavailable_of_obtainable` at this graph: the only way to an unavailable
cell is a query at a sensitive node. -/
theorem not_unavailable_of_obtainable (state : State) {index : Node}
    (hobtain : Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
      index) :
    Available revealed (signedAt state) index := by
  classical
  exact not_not.mp
    (SensitiveQuery.not_unavailable_of_obtainable graph (unavailableAt revealed signedAt)
      (closed revealed signedAt) state hobtain)

/-! ## The WOTS residue is outside what a run can compute

The reduction of a hypertree fault leaves the forgery holding the chain value at a position
strictly below the digit that key's honest message encodes. That cell is unavailable, so by the
closure it is not obtainable either — a run holding it did not derive it, and the only other way
is a query at a sensitive node. -/

/-- **A chain value below the revealed digit is not obtainable.** -/
theorem not_obtainable_wotsPosition (state : State) (key : WotsKey) (chain : Fin chains)
    (position : Fin w) (hbelow : position.val < revealed key chain) :
    ¬ Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
      (.structural (wotsPosition key chain position)) := fun hobtain =>
  not_available_wotsPosition revealed (signedAt state) key chain position hbelow
    (not_unavailable_of_obtainable revealed signedAt state hobtain)

/-! ## The node a sensitive query is at

Reading the corollary the other way: a node the signatures leave a child of unavailable has
exactly one child, so it *is* a `SensitiveNode` and its canonical input is one of the charge's
candidates. -/

open scoped Classical in
/-- The sensitive node a sensitive structural node is. -/
noncomputable def sensitiveNode (hrevealed : ∀ key chain, revealed key chain ≤ w - 1)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    {parent : StructuralNode} (hsensitive : CanonicalGraph.Sensitive revealed signed parent) :
    SensitiveNode :=
  ⟨parent, (singleton_children_of_sensitive revealed signed hrevealed hsensitive).choose,
    (singleton_children_of_sensitive revealed signed hrevealed hsensitive).choose_spec⟩

@[simp] theorem sensitiveNode_parent (hrevealed : ∀ key chain, revealed key chain ≤ w - 1)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    {parent : StructuralNode} (hsensitive : CanonicalGraph.Sensitive revealed signed parent) :
    (sensitiveNode revealed hrevealed signed hsensitive).parent = parent := rfl

/-! ## The digit each hypertree key reveals

Each WOTS key of the hypertree signs exactly one message, and that message is a function of the
key and the seeds alone: the honest node one layer down, or — at the bottom layer — the honest
FORS public key at that leaf. So the revealed digit is fixed before the adversary runs, which is
what lets the WOTS clause be read off the walk rather than off the signing log. -/

variable [HasQuery HashSpec Id]

/-- The message the honest key at `key` signs. -/
def honestMessage (secretSeed publicSeed : Digest) (key : WotsKey) : Digest :=
  match key.tree.layer.val with
  | 0 => value secretSeed publicSeed (.structural (.forsRoots ⟨key.tree.tree, key.leaf⟩))
  | layer + 1 => Extraction.HypertreeChain.honestNode secretSeed publicSeed layer
      (key.tree.tree.val * 2 ^ subtreeHeight + key.leaf.val)

/-- The digit that message encodes on a chain: the position the signature on this key
discloses. -/
def honestRevealed (secretSeed publicSeed : Digest) (key : WotsKey) (chain : Fin chains) : Nat :=
  (Checksum.encode (honestMessage secretSeed publicSeed key) chain).val

/-- **The chain value a signature discloses is available.** The position it opens is the digit
the key's own message encodes, and that digit is what `revealed` records — so the cell at that
position is one the signature has made available, whether it is the chain's start or a value
along it.

The message is the *key's own*, not the forgery's. Read with the wrong one the statement still
typechecks and says nothing: a position the forgery would open need not be one any signature
discloses. -/
theorem available_wotsPosition (revealed : WotsKey → Fin chains → Nat)
    (signed : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (key : WotsKey) (chain : Fin chains) (position : Fin w)
    (hposition : position.val = revealed key chain) :
    CanonicalGraph.Available revealed signed
      (.structural (CanonicalGraph.wotsPosition key chain position)) := by
  rw [CanonicalGraph.wotsPosition]
  split
  · rename_i hzero
    show revealed key chain = 0
    omega
  · rename_i hzero
    show revealed key chain ≤ (position.val - 1) + 1
    omega

/-- A revealed digit never exceeds `w - 1`, which is the only thing the rate needs of it. -/
theorem honestRevealed_le (secretSeed publicSeed : Digest) :
    ∀ (key : WotsKey) (chain : Fin chains),
      honestRevealed secretSeed publicSeed key chain ≤ w - 1 := by
  intro key chain
  have := (Checksum.encode (honestMessage secretSeed publicSeed key) chain).isLt
  simp only [honestRevealed, w, winternitzBits] at this ⊢
  omega

/-! ## The FORS disclosure is coverage or a sensitive query

The split's third branch says the forgery holds the honest FORS secret at every position its
digest selects. A FORS secret is available exactly when its index is in the signed set, so
position by position there are only two possibilities: the signing log selected that index — the
coverage event — or the cell is unavailable, and then by the closure it is not obtainable
either, so the run reached it by a query at a sensitive node.

Nothing here decides which; it is the honest statement of the fork, which is what the gap in
`ForsLeafCharge`'s account was. -/

omit [HasQuery HashSpec Id] in
/-- **An unsigned FORS secret is not obtainable.** -/
theorem not_obtainable_forsPrf (state : State) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) (hunsigned : index ∉ signedAt state key) :
    ¬ Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
      (.structural (.forsPrf key index)) := fun hobtain =>
  hunsigned (not_unavailable_of_obtainable revealed signedAt state hobtain)

/-- The position a FORS tree's selected leaf sits at, as a graph index. -/
def forsIndex (indices : SlhDsaSecurity.Fors.Indices) (tree : Fin forsTrees) :
    Fin (forsTrees * 2 ^ forsHeight) :=
  ⟨Extraction.Fors.leafIndex indices tree, by
    have htree := tree.isLt
    have hleaf := (indices tree).isLt
    have hstep : tree.val * 2 ^ forsHeight + (indices tree).val <
        (tree.val + 1) * 2 ^ forsHeight := by
      rw [Nat.succ_mul]
      omega
    exact lt_of_lt_of_le hstep (Nat.mul_le_mul_right _ htree)⟩

omit [HasQuery HashSpec Id] in
@[simp] theorem forsIndex_val (indices : SlhDsaSecurity.Fors.Indices) (tree : Fin forsTrees) :
    (forsIndex indices tree).val = Extraction.Fors.leafIndex indices tree := rfl

omit [HasQuery HashSpec Id] in
/-- **The FORS disclosure, position by position: signed, or not obtainable.** -/
theorem forsSecret_signed_or_not_obtainable (cache : QueryCache HashSpec)
    (secretSeed : Digest) (key : ForsKey) (indices : SlhDsaSecurity.Fors.Indices)
    (signature : ForsSignature) (state : State)
    (hsecrets : ∀ tree : Fin forsTrees, (signature tree).secret =
      @SlhDsaSecurity.Fors.secret Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed publicSeed key.address (Extraction.Fors.leafIndex indices tree))
    (tree : Fin forsTrees) :
    (signature tree).secret =
        @value (CacheReplay.replayQuery cache) secretSeed publicSeed
          (.structural (.forsPrf key (forsIndex indices tree))) ∧
      (forsIndex indices tree ∈ signedAt state key ∨
        ¬ Obtainable graph (fun other => ¬ unavailableAt revealed signedAt state other)
          (.structural (.forsPrf key (forsIndex indices tree)))) := by
  classical
  refine ⟨(hsecrets tree).trans (@fors_secret_cell (CacheReplay.replayQuery cache) secretSeed
    publicSeed key (forsIndex indices tree)), ?_⟩
  by_cases hsigned : forsIndex indices tree ∈ signedAt state key
  · exact Or.inl hsigned
  · exact Or.inr (not_obtainable_forsPrf revealed signedAt state key _ hsigned)

/-! ## The forgery's own claimed cells, as candidates

Nothing turns a run's transcript into `Obtainable`, and nothing needs to. A forgery that claims
a value for a cell contributes a candidate of its own: `inputOf node value`, which by `inputOf`'s
injectivity in the cell is the node's canonical input exactly when the claimed value is the one
the table gives. So "the forgery holds the unavailable cell" is the same event as "this
candidate is sensitive", and recording the claims alongside the queries charges both at once.

The two shapes of claim are a chain value and a FORS secret, and the nodes above them have
exactly one child whether or not they are sensitive — a chain step's child is the position below
it, a FORS leaf's child is its secret — so the candidates are built unconditionally. -/

/-- The chain-step node above a chain position, which always has exactly one child. -/
def wotsHashNode (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1)) : SensitiveNode :=
  ⟨.wotsHash key chain step,
    .structural (wotsPosition key chain ⟨step.val, by have := step.isLt; omega⟩),
    by by_cases hzero : step.val = 0 <;>
      simp [StructuralNode.children, wotsPosition, hzero]⟩

/-- The FORS leaf node above a FORS secret, which always has exactly one child. -/
def forsLeafNode (key : ForsKey) (index : Fin (forsTrees * 2 ^ forsHeight)) : SensitiveNode :=
  ⟨.forsTree key ⟨0, by omega⟩ ⟨index.val, by simp [index.isLt]⟩,
    .structural (.forsPrf key index), by
      rw [StructuralNode.children, dif_pos rfl]⟩

omit [HasQuery HashSpec Id] in
/-- **A claim at an unavailable cell is a sensitive candidate.** -/
theorem sensitive_inputOf (node : SensitiveNode) (table : Cells) (state : State) (value : Cell)
    (hunavailable : unavailableAt revealed signedAt state node.child)
    (hvalue : value = table node.child) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed node value) :=
  ⟨node, hunavailable, by rw [hvalue]; rfl⟩

omit [HasQuery HashSpec Id] in
/-- **A chain value the forgery claims below the revealed digit is a sensitive candidate.** -/
theorem sensitive_wotsClaim (table : Cells) (state : State) (key : WotsKey)
    (chain : Fin chains) (step : Fin (w - 1)) (value : Cell)
    (hbelow : step.val < revealed key chain)
    (hvalue : value = table (.structural (wotsPosition key chain
      ⟨step.val, by have := step.isLt; omega⟩))) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed (wotsHashNode key chain step) value) :=
  sensitive_inputOf publicSeed revealed signedAt _ table state value
    (not_available_wotsPosition revealed (signedAt state) key chain _ hbelow) hvalue

omit [HasQuery HashSpec Id] in
/-- **A FORS secret the forgery claims at an unsigned position is a sensitive candidate.** -/
theorem sensitive_forsClaim (table : Cells) (state : State) (key : ForsKey)
    (index : Fin (forsTrees * 2 ^ forsHeight)) (value : Cell)
    (hunsigned : index ∉ signedAt state key)
    (hvalue : value = table (.structural (.forsPrf key index))) :
    SensitiveQuery.Sensitive (stakes publicSeed) (unavailableAt revealed signedAt) table state
      (inputOf publicSeed (forsLeafNode key index) value) :=
  sensitive_inputOf publicSeed revealed signedAt _ table state value hunsigned hvalue

/-! ## The record the charge takes

One candidate per claimed cell: the fourteen FORS secrets the signature reveals, and one WOTS
value per layer and chain. The position each WOTS value sits at is the digit that layer's
message encodes, which the residue reduction supplies; it is a parameter here so that the list
is a function of the forgery alone. Its length is a constant — `forsTrees + layers * chains`,
which is `259` — not a function of the budget, which is what makes it affordable. -/

/-- One candidate per cell the forgery claims. -/
def claimedCandidates (forsKey : ForsKey) (indices : SlhDsaSecurity.Fors.Indices)
    (signature : Signature) (keyAt : Fin layers → WotsKey)
    (stepAt : Fin layers → Fin chains → Fin (w - 1)) : List Bytes :=
  (List.finRange forsTrees).map (fun tree =>
      inputOf publicSeed (forsLeafNode forsKey (forsIndex indices tree))
        (signature.fors tree).secret) ++
    (List.finRange layers).flatMap fun layer =>
      (List.finRange chains).map fun chain =>
        inputOf publicSeed (wotsHashNode (keyAt layer) chain (stepAt layer chain))
          ((signature.hypertree layer).wots chain)

omit [HasQuery HashSpec Id] in
/-- The constant, counted rather than estimated. -/
theorem claimedCount : forsTrees + layers * chains = 259 := by decide

omit [HasQuery HashSpec Id] in
/-- **The record's length is a constant.** -/
theorem length_claimedCandidates (forsKey : ForsKey) (indices : SlhDsaSecurity.Fors.Indices)
    (signature : Signature) (keyAt : Fin layers → WotsKey)
    (stepAt : Fin layers → Fin chains → Fin (w - 1)) :
    (claimedCandidates publicSeed forsKey indices signature keyAt stepAt).length =
      forsTrees + layers * chains := by
  simp [claimedCandidates, List.length_flatMap]

end SlhDsaSecurity.GraphStakes

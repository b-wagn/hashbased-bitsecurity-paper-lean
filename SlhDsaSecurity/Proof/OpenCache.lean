import SlhDsaSecurity.Proof.StalledRun
import SlhDsaSecurity.Proof.SensitiveShape
import SlhDsaSecurity.Proof.CanonicalGraph.Programming

/-!
# The handler that answers only what a run may legitimately compute

The charge of `SensitiveQuery` is stated for a run that does not read the cells it is charged
against, and `StalledRun` reduces that to a per-step condition demanded only while the cell in
question is still unavailable. This file supplies the handler that condition is about.

It answers every query with a fresh uniform value, except at the canonical input of a node all
of whose children's cells the signatures make available, which it answers from the table. That
is the most a run may legitimately learn, and `CanonicalGraph.available_of_children_available`
is why it is not more: such a node's own cell is available too, so the answer discloses nothing
the signatures had not already disclosed. The entries it may serve are collected in
`openCache`, which is `CanonicalGraph.Programming.cacheFrom` over the nodes that pass that
test, so the existing lookup and shape lemmas apply to it unchanged.

Two things about the table are easy to get wrong.

* **It is cells *and padding*.** An available node's canonical input is answered with the full
  thirty-byte value, of which only the first sixteen are the node's cell; the other fourteen are
  independent padding. So the thing a run must be blind to is a pair, and `AgreeOff` below is a
  relation on that pair — agreement off one coordinate means agreement on that coordinate's
  cell *and* on that node's padding.
* **A probe names at most one cell.** `SensitiveQuery.Stakes.locate` reads the node off the
  address before any cell is consulted, so the events "this probe is charged against cell `i`"
  are disjoint as `i` ranges over the cells. The sum over cells is therefore a sum over disjoint
  events and contributes one unit per *probe*. Read the other way — stall at each cell, bound at
  each cell, add — it would come to `|Index| · q / 2 ^ 128` and the whole approach would
  collapse.

`openCache_congr_of_agreeOff` is the per-step condition in the form `StalledRun` consumes: at a
state where cell `i` is unavailable, the entries this handler may serve do not mention `i`.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.OpenCache

open CanonicalGraph CanonicalGraph.Programming

/-! ## Two programmed caches that agree -/

/-- Programming the same nodes from tables that give them the same inputs and the same answers
gives the same cache. -/
theorem cacheFrom_congr (publicSeed : Digest) (leftCells rightCells : Cells)
    (leftOutputs rightOutputs : Outputs) (parents : List StructuralNode)
    (cache : QueryCache HashSpec)
    (hkeys : ∀ parent ∈ parents,
      canonicalInput publicSeed leftCells parent = canonicalInput publicSeed rightCells parent)
    (hvalues : ∀ parent ∈ parents, leftOutputs parent = rightOutputs parent) :
    cacheFrom publicSeed leftCells leftOutputs parents cache =
      cacheFrom publicSeed rightCells rightOutputs parents cache := by
  induction parents generalizing cache with
  | nil => rfl
  | cons current rest ih =>
    rw [cacheFrom, cacheFrom, hkeys current (by simp), hvalues current (by simp)]
    exact ih _ (fun other hother => hkeys other (by simp [hother]))
      (fun other hother => hvalues other (by simp [hother]))

/-! ## The entries a run may legitimately read -/

variable (publicSeed : Digest) (available : Node → Prop)

open scoped Classical in
/-- The nodes all of whose children's cells the signatures make available. -/
noncomputable def openNodes : List StructuralNode :=
  Programming.order.filter (fun parent => decide (∀ child ∈ parent.children, available child))

open scoped Classical in
theorem mem_openNodes (parent : StructuralNode) :
    parent ∈ openNodes available ↔ ∀ child ∈ parent.children, available child := by
  rw [openNodes, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Programming.mem_order parent, h⟩⟩

open scoped Classical in
/-- **The entries a run may legitimately read**: the canonical inputs of those nodes, with
their full thirty-byte answers. -/
noncomputable def openCache (table : Cells × Padding) : QueryCache HashSpec :=
  cacheFrom publicSeed table.1 (fullOutput table.1 table.2) (openNodes available) ∅

/-! ## Blindness to one cell

Two tables agreeing everywhere but at one coordinate — its cell and that node's padding — give
the same readable entries, provided that coordinate is unavailable. The keys mention only the
children's cells, which are available; the values mention only the node's own cell, which
`available_of_children_available` makes available too, and its padding. -/

/-- Two tables agreeing off one coordinate: the same cells everywhere else, and the same
padding at every node but that one. -/
def AgreeOff (index : Node) (left right : Cells × Padding) : Prop :=
  (∀ other, other ≠ index → left.1 other = right.1 other) ∧
    ∀ parent : StructuralNode, Node.structural parent ≠ index → left.2 parent = right.2 parent

/-- **The readable entries do not mention an unavailable cell.** -/
theorem openCache_congr_of_agreeOff
    (hclosed : ∀ parent : StructuralNode,
      (∀ child ∈ parent.children, available child) → available (.structural parent))
    (index : Node) (hindex : ¬ available index) (left right : Cells × Padding)
    (hagree : AgreeOff index left right) :
    openCache publicSeed available left = openCache publicSeed available right := by
  classical
  have hne : ∀ other, available other → other ≠ index := fun other hother heq =>
    hindex (heq ▸ hother)
  refine cacheFrom_congr publicSeed _ _ _ _ _ ∅ (fun parent hparent => ?_)
    (fun parent hparent => ?_)
  · refine canonicalInput_congr publicSeed _ _ parent fun child hchild => ?_
    exact hagree.1 child (hne child ((mem_openNodes available parent).mp hparent child hchild))
  · have hcell : available (Node.structural parent) :=
      hclosed parent ((mem_openNodes available parent).mp hparent)
    rw [fullOutput, fullOutput, hagree.1 _ (hne _ hcell), hagree.2 parent (hne _ hcell)]


/-! ## Two availability predicates differ only at the sensitive inputs

The comparison a lazy presentation needs against an eager one is between this handler at the
real availability and the same handler at total availability — the one that answers every
canonical input, which is the eager programmed cache read on demand. They differ at exactly the
canonical inputs of the nodes the real availability calls sensitive, and nowhere else: a
candidate that is not a canonical input is in neither, and a canonical input of a node whose
children are all available is in both with the same answer.

Closure is not what makes this true; it is what makes the handler blind to the unavailable
cells. This is the plainer fact that the readable entries are determined by which nodes pass
the test. -/

open scoped Classical in
/-- **The readable entries at two availability predicates agree off the sensitive inputs.** -/
theorem openCache_congr_of_not_sensitive (lenient strict : Node → Prop)
    (table : Cells × Padding) (input : Bytes)
    (hnot : ∀ parent : StructuralNode, canonicalInput publicSeed table.1 parent = input →
      ((∀ child ∈ parent.children, lenient child) ↔ ∀ child ∈ parent.children, strict child)) :
    openCache publicSeed lenient table input = openCache publicSeed strict table input := by
  classical
  by_cases hcanonical : ∃ parent : StructuralNode,
      canonicalInput publicSeed table.1 parent = input
  · obtain ⟨parent, hparent⟩ := hcanonical
    subst hparent
    rw [openCache, openCache, cacheFrom_lookup, cacheFrom_lookup]
    by_cases hopen : ∀ child ∈ parent.children, lenient child
    · rw [if_pos ((mem_openNodes lenient parent).mpr hopen),
        if_pos ((mem_openNodes strict parent).mpr ((hnot parent rfl).mp hopen))]
    · rw [if_neg (fun hmem => hopen ((mem_openNodes lenient parent).mp hmem)),
        if_neg (fun hmem => hopen ((hnot parent rfl).mpr
          ((mem_openNodes strict parent).mp hmem)))]
  · have hnone : ∀ available : Node → Prop,
        openCache publicSeed available table input = none := by
      intro available
      by_contra hsome
      exact hcanonical ((cacheFrom_empty_canonical publicSeed table.1
        (fullOutput table.1 table.2) (openNodes available) input hsome).imp
        fun parent hparent => hparent.symm)
    rw [hnone lenient, hnone strict]

/-! ## The handler

Its state is the cache, the inputs it has been asked for with the cache each was asked
against, and the number of queries charged — the same shape `SensitiveQuery.probes` records,
so the charge consumes it unchanged. The only new behaviour is that a miss at a readable input
is answered from the table rather than drawn. -/

/-- The cache, the probes with the cache each was issued against, and the charged count. -/
abbrev HandlerState := QueryCache HashSpec × List (Bytes × QueryCache HashSpec) × Nat

open scoped Classical in
/-- **The handler.** Fresh uniform everywhere, except at an input the run may legitimately
read, which is answered from the table. -/
noncomputable def lazyProgram (availableAt : QueryCache HashSpec → Node → Prop)
    (table : Cells × Padding) : QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ←
          (match state.1 input with
            | some cached => (pure (cached, state.1) : ProbComp _)
            | none =>
              match openCache publicSeed (availableAt state.1) table input with
              | some answer => pure (answer, state.1.cacheQuery input answer)
              | none =>
                (fun answer => (answer, state.1.cacheQuery input answer)) <$>
                  ($ᵗ HashOutput : ProbComp HashOutput))
        pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1))

open scoped Classical in
theorem lazyProgram_run_inl (availableAt : QueryCache HashSpec → Node → Prop)
    (table : Cells × Padding) (coin : unifSpec.Domain) (state : HandlerState) :
    ((lazyProgram publicSeed availableAt table) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem lazyProgram_run_inr (availableAt : QueryCache HashSpec → Node → Prop)
    (table : Cells × Padding) (input : Bytes) (state : HandlerState) :
    ((lazyProgram publicSeed availableAt table) (Sum.inr input)).run state =
      (match state.1 input with
        | some cached => (pure (cached, state.1) : ProbComp _)
        | none =>
          match openCache publicSeed (availableAt state.1) table input with
          | some answer => pure (answer, state.1.cacheQuery input answer)
          | none =>
            (fun answer => (answer, state.1.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun step =>
        (pure (step.1, (step.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp _) := rfl

/-- **The step condition `StalledRun` consumes.** At a state where cell `index` is unavailable,
the handler's step does not depend on that cell or on its node's padding. -/
theorem lazyProgram_step_congr (availableAt : QueryCache HashSpec → Node → Prop)
    (hclosed : ∀ (cache : QueryCache HashSpec) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt cache child) →
        availableAt cache (.structural parent))
    (index : Node) (left right : Cells × Padding) (hagree : AgreeOff index left right)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (hindex : ¬ availableAt state.1 index) :
    ((lazyProgram publicSeed availableAt left) queried).run state =
      ((lazyProgram publicSeed availableAt right) queried).run state := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, lazyProgram_run_inl]
  · rw [lazyProgram_run_inr, lazyProgram_run_inr,
      openCache_congr_of_agreeOff publicSeed (availableAt state.1) (hclosed state.1)
        index hindex left right hagree]


/-- **The step condition at the canonical graph.** Availability by the signatures issued so far
is closed under the structure, so the handler never reads an unavailable cell. -/
theorem lazyProgram_step_congr_graph (revealed : WotsKey → Fin chains → Nat)
    (signedAt : QueryCache HashSpec → ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (index : Node) (left right : Cells × Padding) (hagree : AgreeOff index left right)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (hindex : ¬ Available revealed (signedAt state.1) index) :
    ((lazyProgram publicSeed
        (fun cache => Available revealed (signedAt cache)) left) queried).run state =
      ((lazyProgram publicSeed
        (fun cache => Available revealed (signedAt cache)) right) queried).run state :=
  lazyProgram_step_congr publicSeed (fun cache => Available revealed (signedAt cache))
    (fun cache _ hchildren =>
      available_of_children_available revealed (signedAt cache) hchildren)
    index left right hagree queried state hindex


/-! ## The stalled handler is blind to the cell it stalled on

`StalledRun` wants a flag alongside the state, which this handler has no use for, so it is
carried untouched. What comes out is the hypothesis-free form: stalled at the moment the cell
becomes available, the handler's whole run has a law not mentioning that cell. -/

/-- The handler with a flag alongside, which it does not touch. -/
noncomputable def withFlag (impl : QueryImpl OracleWorld (StateT HandlerState ProbComp)) :
    QueryImpl OracleWorld (StateT (HandlerState × Bool) ProbComp) :=
  fun queried state => do
    let step ← (impl queried).run state.1
    pure (step.1, (step.2, state.2))

theorem withFlag_run (impl : QueryImpl OracleWorld (StateT HandlerState ProbComp))
    (queried : OracleWorld.Domain) (state : HandlerState × Bool) :
    ((withFlag impl) queried).run state =
      (impl queried).run state.1 >>= fun step =>
        (pure (step.1, (step.2, state.2)) : ProbComp _) := rfl

/-- **The stalled run does not mention the cell it stalled on.** -/
theorem evalDist_stalled_lazyProgram_congr {α : Type}
    (availableAt : QueryCache HashSpec → Node → Prop)
    (hclosed : ∀ (cache : QueryCache HashSpec) (parent : StructuralNode),
      (∀ child ∈ parent.children, availableAt cache child) →
        availableAt cache (.structural parent))
    (index : Node) (left right : Cells × Padding) (hagree : AgreeOff index left right)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (oa : OracleComp OracleWorld α) (state : HandlerState × Bool) :
    𝒟[(simulateQ (StalledRun.stalled (withFlag (lazyProgram publicSeed availableAt left))
          (fun inner => availableAt inner.1 index) stall) oa).run state] =
      𝒟[(simulateQ (StalledRun.stalled (withFlag (lazyProgram publicSeed availableAt right))
          (fun inner => availableAt inner.1 index) stall) oa).run state] :=
  StalledRun.evalDist_stalled_congr
    (fun table => withFlag (lazyProgram publicSeed availableAt table))
    (fun inner => availableAt inner.1 index) stall (AgreeOff index)
    (fun queried p first second hfirst hfrozen => by
      rw [withFlag_run, withFlag_run,
        lazyProgram_step_congr publicSeed availableAt hclosed index first second hfirst
          queried p.1 hfrozen])
    oa left right hagree state


open scoped Classical in
/-- **The step condition the two-handler comparison takes.** At a query that is not the
canonical input of a node the two availability predicates disagree about, the handler's step is
the same at both. -/
theorem lazyProgram_step_congr_available
    (lenient strict : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (hnot : ∀ input, queried = Sum.inr input →
      ∀ parent : StructuralNode, canonicalInput publicSeed table.1 parent = input →
        ((∀ child ∈ parent.children, lenient state.1 child) ↔
          ∀ child ∈ parent.children, strict state.1 child)) :
    ((lazyProgram publicSeed lenient table) queried).run state =
      ((lazyProgram publicSeed strict table) queried).run state := by
  classical
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, lazyProgram_run_inl]
  · rw [lazyProgram_run_inr, lazyProgram_run_inr,
      openCache_congr_of_not_sensitive publicSeed (lenient state.1) (strict state.1) table input
        (hnot input rfl)]

end SlhDsaSecurity.OpenCache

import SlhDsaSecurity.Proof.WarmedGame
import SlhDsaSecurity.Proof.StructuralTerm
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.CombinedCharge
import SlhDsaSecurity.Proof.TrackedQueries
import SlhDsaSecurity.Proof.GameBridge

/-!
# The charges, at the walk's own cells

With the game split into `WarmedGame.graphWalk` and `WarmedGame.tail`, each charge now applies
to the tail with the cells the walk produced — which is the whole point of walking first. Two
facts are needed to invoke one, and both are about the walk rather than the charge:

* the tail starts from the walk's cache, which carries the canonical entries of those cells
  and nothing else (`CanonicalGraph.Programming.cacheFrom_empty_canonical`), so the
  cleanliness hypothesis every charge takes is discharged;
* the tail's cache growth is bounded by its own charged count, and that count is bounded by
  `q` — which has to be *imported* from the unwarmed game, since `Security.HasTotalBudget`
  speaks about `Security.runAll`. `count_le_of_budget_tail` is that import, and it goes
  through `WarmedGame.evalDist_outcome`: the outcome's law is unchanged by warming, so a
  property holding almost surely there holds on every supported tail here.

`prob_deviatingCollision_tail_le` is the first charge in this form. It is the structural
half of the answer side, now stated against *this run's* honest key rather than an arbitrary
fixed one.
-/

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false
namespace SlhDsaSecurity.WarmedCharges

open Security CanonicalGraph WarmedGame

/-! `afterSeeds` is the whole game after key generation's seeds are drawn, and unfolding it is
never useful here — every statement below treats it as an opaque computation. Left reducible it
is worse than useless: a defeq check as trivial as matching a hypothesis against a syntactically
identical goal unfolds it and does not terminate. -/

attribute [local irreducible] WarmedGame.afterSeeds

/-- A tail result belongs to the warmed run. -/
theorem mem_support_warmedRun {adversary : Adversary}
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    ((walk.1, result.1), result.2) ∈ support (warmedRun adversary) := by
  rw [warmedRun_eq, support_map]
  exact ⟨(walk, result), by
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    exact ⟨walk, hwalk, result, hresult, rfl⟩, rfl⟩

/-- **The budget bounds the tail's count.** -/
theorem count_le_of_budget_tail {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) : result.1.2 ≤ q := by
  have houtcome : result.1 ∈ support ((fun pair => pair.1.2) <$> warmedRun adversary) := by
    rw [support_map]
    exact ⟨_, mem_support_warmedRun hwalk hresult, rfl⟩
  rw [Averaging.support_eq_of_evalDist_eq (evalDist_outcome adversary), support_map] at houtcome
  obtain ⟨inner, hinner, houter⟩ := houtcome
  rw [← houter]
  exact WholeGameStructural.count_le_of_budget hbudget hinner

/-- The walk's cache carries canonical entries and nothing else. -/
theorem walk_cache_canonical
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (input : Bytes) (hinput : walk.2 input ≠ none) :
    ∃ parent : StructuralNode,
      input = canonicalInput walk.1.1.2.2 walk.1.2 parent := by
  obtain ⟨outputs, -, hcache⟩ := mem_support_graphWalk hwalk
  rw [hcache] at hinput
  exact Programming.cacheFrom_empty_canonical _ _ outputs _ input hinput

/-! ## The answer side at the walk's cells

The combined charge takes both answer-side clauses as one predicate so their rate is the
maximum rather than the sum. Carrying it to the tail needs the walk's cache to be *clean* for
that predicate — no entry already witnesses the bad event — and both clauses are dead on a
canonical entry:

* the structural clause asks for a deviating input, and a canonical entry's input is the
  canonical one, so `CanonicalTarget.clean_of_canonical_cache` kills it;
* the coverage clause asks for a message input, and a canonical input is a tweakable input,
  which is a different byte format unless `PK.seed ‖ PK.root` happens to encode a valid
  address. That coincidence is `HashSeparation.Possible`, and it is assumed away here exactly
  as `CombinedCharge.separated_of_not_possible` assumes it away — the same hypothesis
  discharges both, and it is a property of the public key alone. -/

/-- A canonical input is not a message input, the public key being no coincidence. -/
theorem not_messageInput_canonical (publicSeed : Digest) (cells : Cells) (pk : PublicKey)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    (parent : StructuralNode) :
    ¬ CombinedCharge.IsMessageInput pk (canonicalInput publicSeed cells parent) := by
  rintro ⟨randomizer, message, hinput⟩
  rw [canonicalInput] at hinput
  exact HashSeparation.message_tweakable_ne hpublic (hbounds parent) hinput.symm

/-- **The walk's cache is clean for the combined answer-side predicate.** -/
theorem cleanBad_walk_cache (pk : PublicKey)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (hbounds : ∀ parent : StructuralNode, HashSeparation.WithinBounds parent.address)
    (revealed : ForsCoverage.Disclosures)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    GrowthCharge.CleanBad
      (CombinedCharge.CombinedBad walk.1.1.2.2 pk walk.1.2 revealed) walk.2 := by
  intro input output hentry
  obtain ⟨parent, rfl⟩ := walk_cache_canonical hwalk input (by rw [hentry]; simp)
  rintro (hstructural | ⟨hmessage, -⟩)
  · exact CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
      (walk_cache_canonical hwalk) _ output hentry hstructural
  · exact not_messageInput_canonical walk.1.1.2.2 walk.1.2 pk hpublic hbounds parent hmessage

/-! ## The blind cache at the walk

The input half compares the run against the walk's cache with the same run against that cache
*stripped* of its seed-bearing entries — the canonical inputs of the PRF nodes, which are the
only places `SK.seed` appears in the clear. The two caches agree everywhere else, which is what
makes the comparison exact rather than a hop: the probability of touching a stripped input is
the same on both sides, and on the blind side the secret may be drawn after the run.

Stripping is just dropping those nodes from the list the walk programs, so both caches are
`cacheFrom` of the same cells and the same output table, over different node lists. -/

open scoped Classical in
/-- The walk's node list with the seed-bearing nodes removed. -/
noncomputable def blindOrder : List StructuralNode :=
  Programming.order.filter (fun parent => decide (¬ BlindComparison.IsPrfNode parent))

open scoped Classical in
theorem mem_blindOrder (parent : StructuralNode) :
    parent ∈ blindOrder ↔ ¬ BlindComparison.IsPrfNode parent := by
  rw [blindOrder, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Programming.mem_order parent, h⟩⟩

/-- The walk's cache with its seed-bearing entries removed. -/
noncomputable def blindCache (publicSeed : Digest) (cells : Cells)
    (outputs : Programming.Outputs) : QueryCache HashSpec :=
  Programming.cacheFrom publicSeed cells outputs blindOrder ∅

/-- **The walk's cache and its blind twin agree off the inputs carrying the secret.** -/
theorem agreeOff_blindCache (publicSeed : Digest) (cells : Cells)
    (outputs : Programming.Outputs) :
    BlindComparison.AgreeOff
      (TrackedQueries.SeedInputOf (TrackedQueries.prfInput publicSeed)
        (cells CanonicalGraph.Node.secretSeed))
      (Programming.cacheFrom publicSeed cells outputs Programming.order ∅)
      (blindCache publicSeed cells outputs) :=
  TrackedQueries.agreeOff_prfInputs publicSeed cells outputs Programming.order blindOrder
    Programming.mem_order mem_blindOrder

/-- The blind cache really is blind: it holds nothing at an input carrying the secret. -/
theorem blindCache_seedInput_none (publicSeed : Digest) (cells : Cells)
    (outputs : Programming.Outputs) (node : StructuralNode)
    (hprf : BlindComparison.IsPrfNode node) :
    blindCache publicSeed cells outputs
      (TrackedQueries.prfInput publicSeed (cells CanonicalGraph.Node.secretSeed) node) = none := by
  classical
  rw [blindCache, ← TrackedQueries.canonicalInput_eq_prfInput publicSeed cells hprf,
    Programming.cacheFrom_lookup, if_neg (fun hmem => (mem_blindOrder node).mp hmem hprf)]
  rfl

/-! ## The blind cache does not know the secret

The point of stripping the PRF nodes, rather than relabelling them with a dummy seed: what is
left mentions `SK.seed` nowhere. A non-PRF node's canonical input reads only its own children,
and the secret-seed cell is not among them, so the whole blind cache is the same table for
every secret. That is what lets the secret be drawn *after* the blind run, which is what
`SeedDeferral.prob_run_meets_honest_key_le` requires and what a dummy-seed relabelling could
never give — there the dummy is itself a seed the adversary may hunt for, and the comparison
returns the same quantity it was meant to bound. -/

/-- A non-PRF node's canonical input does not read the secret-seed cell. -/
theorem canonicalInput_of_not_prf (publicSeed : Digest) (cells cells' : Cells)
    (hstructural : ∀ parent : StructuralNode,
      cells (CanonicalGraph.Node.structural parent) = cells' (.structural parent))
    {parent : StructuralNode} (hprf : ¬ BlindComparison.IsPrfNode parent) :
    canonicalInput publicSeed cells parent = canonicalInput publicSeed cells' parent := by
  rw [canonicalInput, canonicalInput, CanonicalGraph.childBytes, CanonicalGraph.childBytes]
  refine congrArg _ (congrArg _ (List.map_congr_left fun child hchild => ?_))
  cases child with
  | secretSeed => exact absurd hchild hprf
  | structural inner => rw [hstructural inner]

/-- **The blind cache is the same table for every secret.** -/
theorem blindCache_indep_of_secret (publicSeed : Digest) (outputs : Programming.Outputs)
    (secret secret' : Digest) :
    blindCache publicSeed (Programming.cellsOfOutputs secret outputs) outputs =
      blindCache publicSeed (Programming.cellsOfOutputs secret' outputs) outputs := by
  have hstructural : ∀ parent : StructuralNode,
      Programming.cellsOfOutputs secret outputs (CanonicalGraph.Node.structural parent) =
        Programming.cellsOfOutputs secret' outputs (.structural parent) := fun _ => rfl
  rw [blindCache, blindCache]
  suffices hgeneral : ∀ (parents : List StructuralNode),
      (∀ parent ∈ parents, ¬ BlindComparison.IsPrfNode parent) →
      ∀ cache : QueryCache HashSpec,
        Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secret outputs) outputs
            parents cache =
          Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secret' outputs) outputs
            parents cache from
    hgeneral blindOrder (fun parent hparent => (mem_blindOrder parent).mp hparent) ∅
  intro parents
  induction parents with
  | nil => intro _ cache; rfl
  | cons current parents ih =>
    intro hnone cache
    rw [Programming.cacheFrom, Programming.cacheFrom,
      canonicalInput_of_not_prf publicSeed _ _ hstructural
        (hnone current (List.mem_cons_self ..))]
    exact ih (fun parent hparent => hnone parent (List.mem_cons_of_mem _ hparent)) _

/-! ## The tail's replayed cells are the walk's cells

The structural extraction speaks of `CanonicalGraph.value (replayQuery cache)`, the cells the
*final* cache computes; the charges speak of the walk's cells. They are the same table, and
the reason is the only thing a cache does in this development: it never forgets. The walk
installed a canonical entry at every node, the tail can only add, so the final cache still
answers every canonical query the same way — which by `value_eq_of_cache_agreement` pins the
whole evaluation. -/

/-- The tail can only add to the walk's cache. -/
theorem walk_cache_persists {adversary : Adversary}
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk))
    (input : Bytes) (output : HashOutput) (hentry : walk.2 input = some output) :
    result.2 input = some output := by
  rw [tail] at hresult
  exact GrowthCharge.cache_value_persists _ walk.2 result.2 result.1 hresult input output hentry

/-- **The cells the tail's final cache computes are the walk's own cells.** -/
theorem value_replay_eq_walk_cells (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    @CanonicalGraph.value (CacheReplay.replayQuery result.2) walk.1.1.1 walk.1.1.2.2 =
      walk.1.2 := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  rw [hcells]
  refine GameBridge.value_eq_cellsOfOutputs walk.1.1.2.2 walk.1.1.1 outputs result.2
    fun input output hentry => ?_
  refine walk_cache_persists hresult input output ?_
  rw [hcache, hcells]
  exact hentry

end SlhDsaSecurity.WarmedCharges

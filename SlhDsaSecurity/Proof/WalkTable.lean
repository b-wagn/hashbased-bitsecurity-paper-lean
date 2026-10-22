import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.ReplayGate

/-!
# The walk, as a drawn table

`Obligations.SharedCharged` is stated at `Target.pairedRun`, the walk and the game together,
because the secrets both halves defer — the cell table and `SK.prf` — are the walk's own and
cannot be read once the walk is a parameter. The charges, on the other hand, are proved about a
run that draws its table itself: `RedrawCell.prob_game_sensitive_le` begins
`cells ← $ᵗ Cells; pad ← $ᵗ Padding`, with the table still in the measure when the record is
read.

This file joins the two. The walk *is* a uniform draw of a cells-and-padding pair:
`CanonicalGraph.Programming.warmup_seed_uniform` says so, and `walkOfTable` is the walk that
pair determines — its secret seed is the table's own `secretSeed` cell, its cells are the
table's cells, and its cache is the canonical entries of them. `evalDist_pairedRun` is the whole
of what the shape change costs: one equality of laws, after which the walk's randomness is a
`$ᵗ (Cells × Padding)` the charge can consume.

Two things the presentation has to get right, each of which would be a silent failure.

* **The seed is recovered, not re-drawn.** The walk's value carries the secret seed, and the
  table's law does not. What makes them the same presentation is that on the walk's own support
  the seed is the `secretSeed` cell — the traversal never overwrites it — so the value may be
  read off the table rather than carried beside it. `evalDist_bind_congr_support` is the one
  step where that support fact is used, and it is used in one direction only.
* **The seeds are drawn in the other order.** `WarmedGame.seeds` draws the secret seed first;
  the table's law wants it drawn last, after the public seed its canonical inputs mention. The
  two orders agree because the draws are independent, which is `evalDist_bind_comm` twice and
  nothing else.

`mem_support_graphWalk_walkOfTable` is what keeps the rest of the development usable here. Every
per-walk fact — the budget's bound on the record, the walk's own cache being clean — is stated
for a walk in `support graphWalk`, and a drawn table names such a walk, so none of them has to
be restated at the new shape.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.WalkTable

open Security CanonicalGraph WarmedGame

/-! ## A support-wise congruence under a bind

The seed is recovered from the table on the walk's support, so the step that replaces it has to
be allowed to use where the run can be. -/

/-- **Continuations that agree where the run can be give the same law.** -/
theorem evalDist_bind_congr_support {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a ∈ support oa, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[oa >>= f] x = Pr[= x | oa >>= f] from (probOutput_def _ _).symm,
    show 𝒟[oa >>= g] x = Pr[= x | oa >>= g] from (probOutput_def _ _).symm,
    probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun a => ?_
  by_cases hmem : a ∈ support oa
  · rw [show Pr[= x | f a] = Pr[= x | g a] from by
      rw [probOutput_def, probOutput_def, h a hmem]]
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-! ## The walk a table determines -/

/-- **A table's cells are the cells of its own full output table.** -/
theorem cellsOfOutputs_fullOutput (table : Cells × Padding) :
    Programming.cellsOfOutputs (table.1 Node.secretSeed) (fullOutput table.1 table.2) =
      table.1 := by
  funext node
  cases node with
  | secretSeed => rfl
  | structural parent => exact truncate_fullOutput _ _ _

/-- The walk a cells-and-padding pair determines: the table's own secret seed, the two seeds
drawn beside it, the table's cells, and the canonical entries of those cells. -/
noncomputable def walkOfTable (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec :=
  (((table.1 Node.secretSeed, prfSeed, publicSeed), table.1),
    Programming.cacheFrom publicSeed table.1 (fullOutput table.1 table.2)
      Programming.order ∅)

/-- The walk, drawn as a table. -/
noncomputable def tableWalk :
    ProbComp (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) := do
  let prfSeed ← ($ᵗ Digest : ProbComp Digest)
  let publicSeed ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  pure (walkOfTable prfSeed publicSeed table)

/-- **A drawn table names a walk the run could have taken.** -/
theorem mem_support_graphWalk_walkOfTable (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : walkOfTable prfSeed publicSeed table ∈ support graphWalk := by
  classical
  rw [graphWalk_eq]
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
  refine ⟨(table.1 Node.secretSeed, prfSeed, publicSeed), by simp [seeds],
    (table.1, Programming.cacheFrom publicSeed table.1 (fullOutput table.1 table.2)
      Programming.order ∅), ?_, rfl⟩
  rw [Averaging.support_eq_of_evalDist_eq
    (Programming.warmup_uniform publicSeed (table.1 Node.secretSeed)), support_map]
  refine ⟨fullOutput table.1 table.2, by simp, ?_⟩
  simp only [cellsOfOutputs_fullOutput]

/-! ## The walk's law

The secret seed is read off the table rather than carried beside it, and the three draws are
reordered so the table's own law applies. -/

/-- **The walk's seed is its table's `secretSeed` cell.** -/
theorem secretSeed_of_mem_support (publicSeed secretSeed : Digest)
    (result : Cells × QueryCache HashSpec)
    (hresult : result ∈ support
      ((simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅)) :
    result.1 Node.secretSeed = secretSeed := by
  rw [Averaging.support_eq_of_evalDist_eq (Programming.warmup_uniform publicSeed secretSeed),
    support_map] at hresult
  obtain ⟨outputs, -, houtputs⟩ := hresult
  rw [← houtputs]
  rfl

/-- **The walk at fixed seeds is a drawn table.** -/
theorem evalDist_warmup_table (prfSeed publicSeed : Digest) :
    𝒟[(do
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
        pure (((secretSeed, prfSeed, publicSeed), result.1), result.2))] =
      𝒟[(do
        let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
        pure (walkOfTable prfSeed publicSeed table))] := by
  classical
  have hseed : 𝒟[(do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((secretSeed, prfSeed, publicSeed), result.1), result.2))] =
    𝒟[(do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((result.1 Node.secretSeed, prfSeed, publicSeed), result.1), result.2))] := by
    refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun secretSeed => ?_
    refine evalDist_bind_congr_support _ _ _ fun result hresult => ?_
    rw [secretSeed_of_mem_support publicSeed secretSeed result hresult]
  rw [hseed, ← bind_assoc, evalDist_bind, Programming.warmup_seed_uniform publicSeed,
    ← evalDist_bind, bind_map_left]
  rfl

/-- **The walk is a drawn table.** -/
theorem evalDist_graphWalk : 𝒟[graphWalk] = 𝒟[tableWalk] := by
  classical
  have hwalk : graphWalk = (do
      let secretSeed ← ($ᵗ Digest : ProbComp Digest)
      let prfSeed ← ($ᵗ Digest : ProbComp Digest)
      let publicSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
      pure (((secretSeed, prfSeed, publicSeed), result.1), result.2)) := by
    rw [graphWalk_eq, seeds]
    simp only [bind_assoc, pure_bind]
  rw [hwalk, tableWalk]
  calc 𝒟[(do
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
        pure (((secretSeed, prfSeed, publicSeed), result.1), result.2))]
      = 𝒟[(do
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
        pure (((secretSeed, prfSeed, publicSeed), result.1), result.2))] :=
        OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[(do
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        let secretSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ randomOracle (Programming.warmup publicSeed secretSeed)).run ∅
        pure (((secretSeed, prfSeed, publicSeed), result.1), result.2))] := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun prfSeed => ?_
        exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = _ := by
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun prfSeed => ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun publicSeed => ?_
        exact evalDist_warmup_table prfSeed publicSeed

/-! ## The walk and the game together

The obligation is stated at `Target.pairedRun`, so the law above is read there: the game that
follows is a function of the walk alone, so replacing the walk's law replaces the pair's. -/

/-- The paired run, with the walk drawn as a table. -/
noncomputable def tablePairedRun (adversary : Adversary) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) := do
  let prfSeed ← ($ᵗ Digest : ProbComp Digest)
  let publicSeed ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let result ← tail adversary (walkOfTable prfSeed publicSeed table)
  pure (walkOfTable prfSeed publicSeed table, result)

/-- **The paired run draws its table.** -/
theorem evalDist_pairedRun (adversary : Adversary) :
    𝒟[Target.pairedRun adversary] = 𝒟[tablePairedRun adversary] := by
  rw [Target.pairedRun, tablePairedRun, evalDist_bind, evalDist_graphWalk,
    ← evalDist_bind, tableWalk]
  simp only [bind_assoc, pure_bind]

/-- **Any event at the paired run may be read at the drawn table.** -/
theorem probEvent_pairedRun (adversary : Adversary)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop) :
    Pr[event | Target.pairedRun adversary] = Pr[event | tablePairedRun adversary] :=
  probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_pairedRun adversary)

/-! ## What the obligation reduces to

The two seeds the table does not carry are drawn first and averaged over, so what is left to
prove is a bound at a fixed pair of them with the table still in the measure — which is the
shape the charge is stated in. The secret seed is *not* among the two: it is the table's own
cell, and fixing it is exactly what the obligation may not do. -/

/-- The run the charge reads: a drawn table, the game it determines, and the walk kept. -/
noncomputable def tableRun (adversary : Adversary) (prfSeed publicSeed : Digest) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) := do
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let result ← tail adversary (walkOfTable prfSeed publicSeed table)
  pure (walkOfTable prfSeed publicSeed table, result)

/-- A uniform pair is two uniform draws. -/
theorem uniformSample_prod_eq_bind {α β : Type} [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do
        let left ← ($ᵗ α : ProbComp α)
        let right ← ($ᵗ β : ProbComp β)
        pure (left, right)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-- **The table is drawn as the charge draws it**: the cells first, their padding beside
them. -/
theorem tableRun_eq (adversary : Adversary) (prfSeed publicSeed : Digest) :
    tableRun adversary prfSeed publicSeed = (do
      let cells ← ($ᵗ Cells : ProbComp Cells)
      let pad ← ($ᵗ Padding : ProbComp Padding)
      let result ← tail adversary (walkOfTable prfSeed publicSeed (cells, pad))
      pure (walkOfTable prfSeed publicSeed (cells, pad), result)) := by
  rw [tableRun, uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]

/-- **A bound at each pair of drawn seeds is a bound at the paired run.** This is the whole of
what the obligation's new shape asks for: the cell table and the secret seed it carries stay in
the measure, and only `SK.prf` and the public seed are fixed. -/
theorem probEvent_pairedRun_le (adversary : Adversary)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop) (bound : ℝ≥0∞)
    (hinner : ∀ prfSeed publicSeed, Pr[event | tableRun adversary prfSeed publicSeed] ≤ bound) :
    Pr[event | Target.pairedRun adversary] ≤ bound := by
  rw [probEvent_pairedRun adversary event, tablePairedRun]
  refine WalkDefects.probEvent_bind_le _ _ _ _ fun prfSeed => ?_
  refine WalkDefects.probEvent_bind_le _ _ _ _ fun publicSeed => ?_
  exact hinner prfSeed publicSeed

/-! ## The charge's own pairing

`RedrawCell.prob_game_sensitive_le` reads its run as `(result, cells)`: the result first, the
cells beside it, and the **padding dropped**. `tableRun` reads it as `(walk, result)`, and the
walk's cache is a function of the cells *and* the padding — so the walk is not recoverable from
the charge's pairing, and the reindexing between the two is not the identity rearrangement it
looks like.

What makes it one is a property of the event rather than of the pairing: the obligation's event
never reads the walk's cache. `Target.GoodWalk` reads the seeds and the cells;
`RoutedSplit.Trace` — what both `InputBad` and `RandomiserBad` are stated at — is built from
the walk's *value* and the tail's result, and has no component for the walk's cache at all. So
`CacheBlind` holds for it by `Iff.rfl`, and that is the hypothesis the reindexing takes rather
than a fact it assumes. An event that did read the walk's cache would not cross this step, and
would fail here rather than silently. -/

/-- An event the walk's cache does not reach. -/
def CacheBlind (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
    ((Outcome × Nat) × QueryCache HashSpec)) → Prop) : Prop :=
  ∀ (value : (Digest × Digest × Digest) × Cells) (cache cache' : QueryCache HashSpec)
    (result : (Outcome × Nat) × QueryCache HashSpec),
      event ((value, cache), result) ↔ event ((value, cache'), result)

/-- The event read at the charge's pairing: the seeds rebuilt from the cells, and any cache at
all, which `CacheBlind` makes immaterial. -/
def reduce (prfSeed publicSeed : Digest)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop)
    (z : ((Outcome × Nat) × QueryCache HashSpec) × Cells) : Prop :=
  event ((((z.2 Node.secretSeed, prfSeed, publicSeed), z.2), ∅), z.1)

/-- The run the charge reads, paired as the charge pairs it. -/
noncomputable def chargeRun (adversary : Adversary) (prfSeed publicSeed : Digest) :
    ProbComp (((Outcome × Nat) × QueryCache HashSpec) × Cells) := do
  let cells ← ($ᵗ Cells : ProbComp Cells)
  let pad ← ($ᵗ Padding : ProbComp Padding)
  let result ← tail adversary (walkOfTable prfSeed publicSeed (cells, pad))
  pure (result, cells)

open scoped Classical in
/-- **The two pairings read a cache-blind event alike.** -/
theorem probEvent_tableRun_eq (adversary : Adversary) (prfSeed publicSeed : Digest)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop) (hblind : CacheBlind event) :
    Pr[event | tableRun adversary prfSeed publicSeed] =
      Pr[reduce prfSeed publicSeed event | chargeRun adversary prfSeed publicSeed] := by
  rw [tableRun_eq, chargeRun, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun cells => congrArg _ ?_
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun pad => congrArg _ ?_
  rw [bind_pure_comp, bind_pure_comp, probEvent_map, probEvent_map]
  exact probEvent_congr' (fun result _ =>
    hblind ((cells Node.secretSeed, prfSeed, publicSeed), cells) _ ∅ result) rfl

/-- **A bound at the charge's pairing is a bound at the paired run.** -/
theorem probEvent_pairedRun_le_of_charge (adversary : Adversary)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop) (hblind : CacheBlind event)
    (bound : ℝ≥0∞)
    (hinner : ∀ prfSeed publicSeed,
      Pr[reduce prfSeed publicSeed event | chargeRun adversary prfSeed publicSeed] ≤ bound) :
    Pr[event | Target.pairedRun adversary] ≤ bound := by
  refine probEvent_pairedRun_le adversary event bound fun prfSeed publicSeed => ?_
  rw [probEvent_tableRun_eq adversary prfSeed publicSeed event hblind]
  exact hinner prfSeed publicSeed

/-! ## The shared obligation at the charge's pairing

The obligation's own event crosses, and what is left to prove is a bound on `SharedReduced` at
each pair of seeds — one statement about a drawn table, the run it determines, and the forgery
that run returns. -/

open RoutedSplit ReplayGate in
/-- The shared obligation's event, read at the charge's pairing. -/
def SharedReduced (prfSeed publicSeed : Digest)
    (z : ((Outcome × Nat) × QueryCache HashSpec) × Cells) : Prop :=
  reduce prfSeed publicSeed (fun pair => Target.GoodWalk pair.1 ∧
    (InputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
      RandomiserBad ((pair.1.1, pair.2.1), pair.2.2))) z

open RoutedSplit ReplayGate in
/-- **Where every index lands.** The reduced event spelled out: the two seeds are the ones held
fixed, the secret seed and the cells are the drawn table's, and the trace the two defects are
read at is built from those together with the tail's own result. It is `Iff.rfl`, which is the
point — an index that slipped would fail here rather than inside the chain. -/
theorem sharedReduced_iff (prfSeed publicSeed : Digest)
    (z : ((Outcome × Nat) × QueryCache HashSpec) × Cells) :
    SharedReduced prfSeed publicSeed z ↔
      ((prfSeed ≠ publicSeed ∧ ¬ HashSeparation.Possible
          (publicSeed, z.2 (.structural WalkDefects.topNode))) ∧
        (InputBad ((((z.2 Node.secretSeed, prfSeed, publicSeed), z.2), z.1.1), z.1.2) ∨
          RandomiserBad ((((z.2 Node.secretSeed, prfSeed, publicSeed), z.2), z.1.1), z.1.2))) :=
  Iff.rfl

open RoutedSplit ReplayGate in
/-- **The shared obligation's event does not read the walk's cache.** -/
theorem cacheBlind_shared : CacheBlind (fun pair => Target.GoodWalk pair.1 ∧
    (InputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
      RandomiserBad ((pair.1.1, pair.2.1), pair.2.2))) :=
  fun _ _ _ _ => Iff.rfl

open RoutedSplit ReplayGate in
/-- **The shared obligation, reduced to a bound at the charge's own pairing.** -/
theorem probEvent_shared_le (adversary : Adversary) (bound : ℝ≥0∞)
    (hinner : ∀ prfSeed publicSeed,
      Pr[SharedReduced prfSeed publicSeed | chargeRun adversary prfSeed publicSeed] ≤ bound) :
    Pr[fun pair => Target.GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
          RandomiserBad ((pair.1.1, pair.2.1), pair.2.2)) |
      Target.pairedRun adversary] ≤ bound :=
  probEvent_pairedRun_le_of_charge adversary _ cacheBlind_shared bound hinner

end SlhDsaSecurity.WalkTable

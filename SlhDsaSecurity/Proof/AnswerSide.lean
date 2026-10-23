import SlhDsaSecurity.Proof.RoutedSplit
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.AddressBounds
import SlhDsaSecurity.Proof.WalkDefects
import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.CoverageCount
import SlhDsaSecurity.Proof.SplitWitness

/-!
# The answer side, as one predicate against one budget

The target takes the answer side as a single hypothesis: one predicate, one bound. What exists
below it is two charges that were stated separately, and the reason they cannot simply be added
is the budget. Each is linear in a query count, and charging both against the whole budget
would spend `2 q / 2 ^ 128`, which is the entire target twice over.

They do not have to be. A deviating structural collision is witnessed at a *canonical* input
and the coverage event at a *message* input, and those two classes are disjoint as byte
formats as soon as the public key is no coincidence — `CombinedCharge.separated_of_not_possible`
is that separation, and `AddressBounds.withinBounds_structural` discharges the address side of
it outright, so the only hypothesis left on the key is `hpublic`.

So the structural charge is restated here against the *outside* class only: with
`ClassCharge.prob_badWithinClasses_le`, a message-class query is charged at rate zero, because
on a message input the canonical target does not exist at all. The coverage charge is already
class-counted, at the message class, by `CoverageTail.prob_coverage_tail_le`. The two counts
then add to the growth of the run rather than each equalling it, and one budget covers both.

`pk` stays free throughout. It is the real key only when the routing instantiates it, and
keeping it free here is what keeps `hpublic` a hypothesis about a public key rather than a
statement about key generation.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerSide

open Security CanonicalGraph WarmedGame

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

/-- The structural clause as a per-answer predicate: this answer hits the canonical cell of the
node its own input names, the input's child values deviating from the honest ones. -/
noncomputable def CanonicalBad (publicSeed : Digest) (cells : Cells) :
    Bytes → HashOutput → Prop :=
  fun input answer =>
    CanonicalTarget.canonicalTarget publicSeed cells input = some (Hashing.truncate answer)

/-- **Off the message class the rate is one unit of `2 ^ -128`.** -/
theorem prob_canonicalBad_le (publicSeed : Digest) (cells : Cells) (input : Bytes) :
    Pr[fun answer : HashOutput => CanonicalBad publicSeed cells input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (probEvent_mono fun _ _ hbad => hbad.symm)
    (FreshHitBound.prob_target_match_le (CanonicalTarget.canonicalTarget publicSeed cells input))

/-! ## The two charges against one budget

`prob_answerBad_le` below takes the two class limits as two numbers and leaves their sum to be
discharged against the budget. That sum cannot be discharged: the split between the classes is
the adversary's to choose, run by run, and the only pair of fixed numbers that bounds both
growths on *every* run is `budget, budget` — the target twice over.

So the sum has to be taken before the uniform bound rather than after.
`ClassExpectation.prob_bad_or_coverage_le` is that step: the two counts are read off one
split-counted run, added pathwise, and bounded once. The structural charge it needs is proved
there; the coverage charge has to arrive already in expectation form, and that is the one thing
this route still owes — see the note below. -/

/-! ## The answer side with its coverage charge closed

`prob_answerBad_le_of_budget` above takes the coverage charge in expectation form as a
hypothesis, because when it was written nobody had it. `AnswerCoverage` has it now, at the
game's own recorder tests, and this is the same statement with that hypothesis discharged.

What the conclusion carries instead is `¬ SeedRandomised`. That is the narrowing's leftover —
the cache holding a message input whose randomiser is `SK.prf` — and it cannot be charged here
at all: the seed belongs to the walk, this statement is read at a fixed walk where it is
already determined, and an adversary may carry it as a constant. It is conjoined so that the
shared half can charge it where the seed is still random, and so that nobody mistakes it for
something this side paid.

`hdisclosing` is the other thing left visible. The split states disclosure at the signing log —
a digest discloses when the signer served the request it belongs to — while the recorder has to
decide a query when it answers it, with only the cache in hand, so its test is that the cache
holds the `PRF_msg` entry the randomiser comes from. Both occurrences of the notion move at
once, the witnesses and the target's negation, so the two have to agree rather than be ordered.
Left to right is the log's faithfulness: the signer queried `PRF_msg` for what it served and
the cache keeps the answer. Right to left is the randomiser defect's absence: a cached
`PRF_msg` entry at the real seed for a framing no request produced would be disclosing to the
recorder and served by nobody. Charging that is the shared half's business, where the seed is
still random, which is why it is a hypothesis here rather than a step. -/

/-! ## The same charge, before the recordings are forgotten

`prob_answerBad_le_of_caps` concludes at the tail, where the recordings are gone, and so has to
assume the ordering defect never fires on the support. The assembly no longer wants that
assumption — it wants the defect's absence charged, which means carrying it as a conjunct of the
event, which means stating the bound where a conjunct about the recordings is expressible.

That place is the recorded run, one step earlier, and `AnswerCoverage` already has the two
charges there. The only thing that moves with them is `hdisclosing`, which is read pointwise at
each supported result and therefore follows wherever the support is read. -/

/-! ## The same charge with the leftover narrowed to the forgery

`prob_answerBad_le_of_caps_recorded` carries `¬ SeedRandomised`, which is about the whole cache
and so costs one unit per query — a price the ledger's `q` coefficient, saturated at two, cannot
pay. `AnswerCoverage.ForgerySeedRandomised` is the same leftover read at the forgery alone, which
is one object and therefore one constant. This is that charge with the narrow conjunct in place of
the wide one; nothing else moves, and the bound does not change. -/

/-! ## The two charges, added

The coverage charge is already counted on the message class, so the two counts are the two
sides of one split rather than two copies of the budget. What they add to is the growth of the
tail, which is what the target's `q - 2 ^ subtreeHeight` is. -/

/-! ## The key the charge is stated at

The charge needs the key fixed before the tail runs, and the routing names the key this run's
own final cache generates. They agree: after the graph is walked, key generation asks the cache
nothing new, so the key is already determined by the walk and the tail cannot move it. -/

set_option maxHeartbeats 1000000 in
/-- **The key the run generates is the key the walk already fixed.** -/
theorem generatedKey_eq_walk (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2 =
      SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2 := by
  obtain ⟨outputs, hwarm⟩ := HonestGrowth.walk_cache_eq_warmCache hwalk
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (afterSeeds adversary walk.1.1))).run walk.2) := hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, -⟩ :=
    WarmedSplit.split_afterSeeds adversary walk.1.1 walk.2 result hrun
  have hpure := hkeys
  rw [hwarm, HonestProbes.run_keygenInternal_world_eq_pure, support_pure,
    Set.mem_singleton_iff] at hpure
  have hvalue : keys = @Scheme.keygenInternal Id Id.instMonad
      (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 := by
    rw [hwarm]; exact (Prod.ext_iff.mp hpure).1
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  have hreplay := WarmedSplit.keygenInternal_eq_replay_of_subset walk.1.1.1 walk.1.1.2.1
    walk.1.1.2.2 walk.2 keyCache result.2 keys hkeys hpersist
  rw [SplitCharged.generatedKey, SplitCharged.generatedKey, ← hreplay, hvalue]

/-! ## The hypothesis on the key is the walk's own

`hpublic` is a statement about the key the game generates, and the walk already pays for it:
its public seed is the seed the walk drew and its root is the walk's own cell at the top node.
So the charge's hypothesis is the walk defect `WalkDefects.prob_possible_walk` charges, and
nothing further is owed for it. -/

/-- **The walk's cache computes the walk's cells.** -/
theorem value_replay_walk_eq_cells
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    @CanonicalGraph.value (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.2 =
      walk.1.2 := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  rw [hcells]
  refine GameBridge.value_eq_cellsOfOutputs walk.1.1.2.2 walk.1.1.1 outputs walk.2
    fun input output hentry => ?_
  rw [hcache, hcells]
  exact hentry

/-- **The generated key is the walk's seed and the walk's top cell.** -/
theorem generatedKey_eq_walk_pair
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ((SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed,
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root) =
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)) := by
  have hseed : (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed =
      walk.1.1.2.2 :=
    (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).1
  have hroot : (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root =
      walk.1.2 (.structural WalkDefects.topNode) := by
    rw [SplitCharged.generatedKey,
      (GameBridge.keygen_publicKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).2,
      ← @WalkDefects.value_topNode (CacheReplay.replayQuery walk.2) walk.1.1.1 walk.1.1.2.2,
      value_replay_walk_eq_cells hwalk]
  rw [hseed, hroot]

/-- **The key is no coincidence as soon as the walk is not one.** -/
theorem not_possible_generatedKey
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hgood : ¬ HashSeparation.Possible
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode))) :
    ¬ HashSeparation.Possible
      ((SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed,
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root) := by
  rw [generatedKey_eq_walk_pair hwalk]
  exact hgood

/-! ## What the target asks for

The shape the target's `hanswer` is stated in, with the two class counts as hypotheses. This is
the whole of what the answer side still owes: one pair of numbers whose sum is the growth the
tail is allowed. The `2 ^ -126` the target allows for a load cap is not spent — on this route
the coverage clause is charged against the recording rather than against a fixed disclosure
set, so what it costs is the recording's own `2 ^ -141` and nothing more. -/

/-! ## The answer side at a good walk, with the coverage charge closed

`prob_answerBad_le_of_caps` is read at a key fixed before the tail runs;
`Obligations.AnswerCharged` is read at the key the run's own cache generates, on a walk that is
no coincidence, against the experiment's budget. The three steps between are the ones the older
chain already takes — the generated key is the walk's own (`generatedKey_eq_walk`), the walk's
own coincidence is the key's (`not_possible_generatedKey`), and the budget bounds the tail's
count (`WarmedCharges.count_le_of_budget_tail`) — so this is that chain with the coverage
hypothesis gone.

The bound is stated tight, at `q / 2 ^ 128 + 2 ^ -141`. The target's `2 ^ -126` is its defect
allowance and nothing on this route needs it, so it is left for whatever does — which, as it
turns out, is the narrowing's leftover when the obligation is finally assembled. -/

/-! ## The same thing at a good walk, still at the recorded run

The three steps are the ones the older chain takes — the generated key is the walk's own, the
walk's coincidence is the key's, the budget bounds the tail's count — and only the first needs
anything new, because it is read at a supported result and the support is now the recorder's.
`CoverageCount.mem_support_rom_of_recorderOf` carries a recorded result to the tail result it
forgets to, which is exactly what that step wants. -/

/-! ## And at a good walk, with the leftover narrowed

The same three steps as the wide version — the generated key is the walk's own, the walk's
coincidence is the key's, the budget bounds the tail's count — and the leftover travels as a
conjunct rather than as a probability bound, because at a fixed walk it has no probability bound.
Averaged over the walk it has one, and it is a constant, which is the point of narrowing it to a
single object. -/

/-! ## The same charge at a good walk, with the narrowed class a parameter

`AnswerCoverage.prob_bad_or_coverage_le_of_caps_recorded_class` carries the class demand as a
conjunct instead of naming the leftover, and this is that at the walk's own key. The three steps
between are the usual ones and none of them reads the class.

At `SplitWitness.narrowClass` the conjunct is the leftover and `AnswerJoin` charges it; at
`CombinedCharge.IsMessageInput` it holds of every result and drops. The point of the parameter is
that moving between those two is an instantiation. -/

end SlhDsaSecurity.AnswerSide

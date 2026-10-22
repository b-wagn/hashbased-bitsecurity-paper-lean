import SlhDsaSecurity.Proof.RoutedSplit
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.AddressBounds
import SlhDsaSecurity.Proof.WalkDefects

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

/-- **On a message input there is nothing to hit.** The canonical target is `none` there, the
public key being no coincidence, so a message-class query is charged at rate zero. -/
theorem prob_canonicalBad_message_eq_zero (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    (input : Bytes) (hmessage : CombinedCharge.IsMessageInput pk input) :
    Pr[fun answer : HashOutput => CanonicalBad publicSeed cells input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 0 := by
  refine le_of_eq (probEvent_eq_zero fun answer _ hbad => ?_)
  rw [CanonicalBad, CombinedCharge.separated_of_not_possible publicSeed pk cells hpublic
    withinBounds_structural input hmessage] at hbad
  exact absurd hbad (by simp)

/-- **Off the message class the rate is one unit of `2 ^ -128`.** -/
theorem prob_canonicalBad_le (publicSeed : Digest) (cells : Cells) (input : Bytes) :
    Pr[fun answer : HashOutput => CanonicalBad publicSeed cells input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (probEvent_mono fun _ _ hbad => hbad.symm)
    (FreshHitBound.prob_target_match_le (CanonicalTarget.canonicalTarget publicSeed cells input))

set_option maxHeartbeats 1000000 in
/-- **The structural term, charged on the class it lives in.** The collision is witnessed at a
canonical input, so only the queries outside the message class pay for it. -/
theorem prob_deviatingCollision_outside_le (adversary : Adversary) (pk : PublicKey)
    (qs qm : Nat) (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput pk) walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput pk input)
        walk.2 result.2 qs) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result | tail adversary walk] ≤
      (qs : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hcharge := ClassCharge.prob_badWithinClasses_le
    (countAllHashes (afterSeeds adversary walk.1.1))
    (CanonicalBad walk.1.1.2.2 walk.1.2) (CombinedCharge.IsMessageInput pk)
    0 (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) qm qs walk.2
    (fun input hmessage => prob_canonicalBad_message_eq_zero walk.1.1.2.2 pk walk.1.2 hpublic
      input hmessage)
    (fun input _ => prob_canonicalBad_le walk.1.1.2.2 walk.1.2 input)
    (CanonicalTarget.clean_of_canonical_cache walk.1.1.2.2 walk.1.2 walk.2
      (WarmedCharges.walk_cache_canonical hwalk))
  rw [mul_zero, zero_add, mul_one_div] at hcharge
  rw [tail]
  refine le_trans (probEvent_mono ?_) hcharge
  rintro result hresult ⟨candidates, parent, output, hdeviates, hentry, hcollision⟩
  have hres : result ∈ support (tail adversary walk) := by rw [tail]; exact hresult
  exact ⟨CanonicalTarget.hit_of_deviating_collision walk.1.1.2.2 walk.1.2 candidates parent
    result output hdeviates hentry hcollision, hinside result hres, houtside result hres⟩

/-! ## The two charges, added

The coverage charge is already counted on the message class, so the two counts are the two
sides of one split rather than two copies of the budget. What they add to is the growth of the
tail, which is what the target's `q - 2 ^ subtreeHeight` is. -/

set_option maxHeartbeats 1000000 in
/-- **The answer side, as one predicate with one bound.** -/
theorem prob_answerBad_le (adversary : Adversary) (pk : PublicKey) (qs qm : Nat)
    (hqm : qm ≤ 5 * 2 ^ 62) (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root))
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput pk) walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput pk input)
        walk.2 result.2 qs) :
    Pr[fun result => RoutedSplit.AnswerBadAt pk ((walk.1, result.1), result.2) |
      tail adversary walk] ≤
      ((qs + qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) := by
  calc Pr[fun result => RoutedSplit.AnswerBadAt pk ((walk.1, result.1), result.2) |
        tail adversary walk]
      ≤ Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
            StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result ∨
              CoverageTail.ForgeryCovered pk result | tail adversary walk] :=
        probEvent_mono fun result _ hbad =>
          hbad.imp id (CoverageRouted.forgeryCovered_of_disclosed walk.1.1.2.1 pk result)
    _ ≤ Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
            StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result |
          tail adversary walk] +
          Pr[CoverageTail.ForgeryCovered pk | tail adversary walk] := probEvent_or_le _ _ _
    _ ≤ (qs : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / 2 ^ 141 + (qm : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        add_le_add
          (prob_deviatingCollision_outside_le adversary pk qs qm hpublic hwalk hinside houtside)
          (CoverageTail.prob_coverage_tail_le adversary pk qm hqm hpublic
            withinBounds_structural hwalk hinside)
    _ = ((qs + qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) := by
        rw [show ((2 ^ 141 : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 141 from by push_cast; ring,
          Nat.cast_add, ← ENNReal.div_add_div_same]
        ring

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

set_option maxHeartbeats 1000000 in
/-- **The answer side at the run's own key.** -/
theorem prob_answerBad_generated_le (adversary : Adversary) (qs qm : Nat)
    (hqm : qm ≤ 5 * 2 ^ 62)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hpublic : ¬ HashSeparation.Possible
      ((SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).seed,
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2).root))
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input)
        walk.2 result.2 qs) :
    Pr[fun result => RoutedSplit.AnswerBad ((walk.1, result.1), result.2) |
      tail adversary walk] ≤
      ((qs + qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (prob_answerBad_le adversary _ qs qm hqm hpublic hwalk hinside houtside)
  intro result hresult hbad
  rw [RoutedSplit.AnswerBad, RoutedSplit.keyOf,
    generatedKey_eq_walk adversary hwalk hresult] at hbad
  exact hbad

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

set_option maxHeartbeats 1000000 in
/-- **The answer side on a good walk.** This is the target's `hanswer` but for the budget: what
is left is the number the two class counts add to. -/
theorem prob_answerBad_good_le (adversary : Adversary) (qs qm : Nat)
    (hqm : qm ≤ 5 * 2 ^ 62)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hgood : ¬ HashSeparation.Possible
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)))
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input)
        walk.2 result.2 qs) :
    Pr[fun result => RoutedSplit.AnswerBad ((walk.1, result.1), result.2) |
      tail adversary walk] ≤
      ((qs + qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) :=
  prob_answerBad_generated_le adversary qs qm hqm hwalk
    (not_possible_generatedKey hwalk hgood) hinside houtside

/-! ## What the target asks for

The shape the target's `hanswer` is stated in, with the two class counts as hypotheses. This is
the whole of what the answer side still owes: one pair of numbers whose sum is the growth the
tail is allowed. The `2 ^ -126` the target allows for a load cap is not spent — on this route
the coverage clause is charged against the recording rather than against a fixed disclosure
set, so what it costs is the recording's own `2 ^ -141` and nothing more. -/

set_option maxHeartbeats 1000000 in
/-- **The answer side at the target's own bound**, given the class counts. -/
theorem prob_answerBad_le_of_classes (adversary : Adversary) (q qs qm : Nat)
    (hsum : qs + qm ≤ q - 2 ^ subtreeHeight) (hqm : qm ≤ 5 * 2 ^ 62)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    (hgood : ¬ HashSeparation.Possible
      (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)))
    (hinside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        walk.2 result.2 qm)
    (houtside : ∀ result ∈ support (tail adversary walk),
      ClassCharge.GrowthAtMostOn (fun input => ¬ CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input)
        walk.2 result.2 qs) :
    Pr[fun result => RoutedSplit.AnswerBad ((walk.1, result.1), result.2) |
      tail adversary walk] ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
          (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)) := by
  refine le_trans (prob_answerBad_good_le adversary qs qm hqm hwalk hgood hinside houtside)
    (add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hsum) _) le_add_self)

end SlhDsaSecurity.AnswerSide

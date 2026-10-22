import SlhDsaSecurity.Proof.CoverageCount
import SlhDsaSecurity.Proof.SplitWitness

/-!
# The answer half's two charges, at the game's own tests

`CoverageCount.prob_bad_or_coverage_le_of_join` leaves three things: the join from the game's
coverage event to `BlockViews.TargetCovered`, and the two recording caps. This file supplies the
join at the game's recorder tests and the target cap from the budget. What it does not supply —
deliberately — is the narrowing's leftover.

**The leftover is not charged here and must not be.** `SplitWitness.mem_records_or_seedRandomised`
returns a disjunction: either the recordings hold the target and its witnesses, or the cache
holds a message input whose randomiser is `SK.prf`. The second is a guess at a secret the walk
drew, and these statements are read at a *fixed* walk, where that secret is already determined —
an adversary may carry it as a constant. Charging it here would be a false statement in a small
place. So it is conjoined to the event, visibly, and the shared half charges it where the seed is
still random.

The disclosing cap is likewise left as a hypothesis. It says the signer-randomised recording is
no longer than the signing limit, which is a fact about how many requests were served rather
than about this charge.

`inClass` stays a parameter, but the class it is meant at is the message class: at
`CombinedCharge.IsMessageInput pk`, the hypothesis `hrightClass` is exactly
`SplitWitness.targetKeep_class`, and `hbadClass` is the separation the structural clause is
already stated against.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerCoverage

open Security DigestTape ClassGrowth CoverageCount

/-! ## The join at the game's tests -/

open scoped Classical in
/-- **The join, with the leftover excluded rather than paid.** -/
theorem targetCovered_of_forgeryDisclosedCovered (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (computation : OracleComp OracleWorld Outcome) (cache : QueryCache HashSpec)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (result : (Outcome × Counts) × SplitPrefix.SplitState)
    (hmem : result ∈ support (BlockViews.recordedRun
      (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
      (countQueries (splitCost inClass inside outside) computation) cache))
    (hlate : ¬ SplitWitness.LateDisclosure prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hcovered : SplitWitness.CoveredAtKeep prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hseed : ¬ SplitWitness.SeedRandomised prfSeed pk result.2.1) :
    BlockViews.TargetCovered result := by
  classical
  rcases SplitWitness.mem_records_or_seedRandomised prfSeed pk (countAllHashes computation)
      cache ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)
      (by
        rw [← RecorderView.recorderOf_cache]
        exact mem_support_recorder_countAllHashes (SplitWitness.disclosingKeep prfSeed pk)
          (SplitWitness.targetKeep prfSeed pk) inClass hne computation (cache, [], []) result hmem)
      hfresh hlate hcovered with hleftover | ⟨target, htarget, hwitness⟩
  · exact absurd hleftover hseed
  · refine ⟨target, htarget, fun tree => ?_⟩
    obtain ⟨witness, hmember, -, hinstance, hleaf⟩ := hwitness tree
    exact ⟨witness, hmember, hinstance, hleaf⟩

/-! ## Both charges, at the game's tests -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, against one budget.** The structural clause is paid by the
outside slot of the split counter and the coverage clause by the inside slot, so the budget
bounds their sum on every run and the bound is `budget / 2 ^ 128 + 1 / 2 ^ 141`.

The coverage clause carries `¬ SeedRandomised` with it. That is the narrowing's leftover, left
visible: the shared half charges it, where the seed the guess is against is still random. -/
theorem prob_bad_or_coverage_le_of_caps (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      SplitWitness.targetKeep prfSeed pk input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      initialCache input = none)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hlate : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      ¬ SplitWitness.LateDisclosure prfSeed pk
        ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        GrowthCharge.Bad bad result ∨
          (SplitWitness.CoveredAtKeep prfSeed pk result ∧
            ¬ SplitWitness.SeedRandomised prfSeed pk result.2) |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join inClass hne
    (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
    hrightClass bad hrate hbadClass computation initialCache hclean
    (fun result => SplitWitness.CoveredAtKeep prfSeed pk result ∧
      ¬ SplitWitness.SeedRandomised prfSeed pk result.2)
    leftLength budget hcap (fun result hmem hcoverage => ?_) hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne hrightClass computation
      initialCache result hmem budget hbudget)
    budget hbudget
  exact targetCovered_of_forgeryDisclosedCovered prfSeed pk inClass hne computation initialCache
    hfresh result hmem (hlate result hmem) hcoverage.1 hcoverage.2

/-! ## The same two charges, before the recordings are forgotten

The shape above concludes at the shared oracle's run, so its coverage clause can only mention
the result and the cache. The ordering defect mentions the target recording, and the repair the
assembly now wants is to stop assuming it never fires and make its absence a *conjunct* of the
charged event instead. That cannot be written at the shared oracle's run at all.

So the same charge is taken one step earlier, at the recorded run, where all three conjuncts are
expressible: the coverage event, the narrowing's leftover, and the ordering defect's absence.
Nothing about the argument changes — `targetCovered_of_forgeryDisclosedCovered` already reads
all three pointwise, which is why the move costs nothing. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges at the recorded run**, with the ordering defect's absence
carried inside the coverage clause rather than assumed of the support. -/
theorem prob_bad_or_coverage_le_of_caps_recorded (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      SplitWitness.targetKeep prfSeed pk input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      initialCache input = none)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad (result.1, result.2.1) ∨
          (SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
            ¬ SplitWitness.SeedRandomised prfSeed pk result.2.1 ∧
            ¬ SplitWitness.LateDisclosure prfSeed pk result) |
        BlockViews.recordedRun
          (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
          (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join_recorded inClass hne
    (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
    hrightClass bad hrate hbadClass computation initialCache hclean
    (fun result => SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
      ¬ SplitWitness.SeedRandomised prfSeed pk result.2.1 ∧
      ¬ SplitWitness.LateDisclosure prfSeed pk result)
    leftLength budget hcap (fun result hmem hcoverage => ?_) hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne hrightClass computation
      initialCache result hmem budget hbudget)
    budget hbudget
  exact targetCovered_of_forgeryDisclosedCovered prfSeed pk inClass hne computation initialCache
    hfresh result hmem hcoverage.2.2 hcoverage.1 hcoverage.2.1

/-! ## The leftover, narrowed to the one object that can be charged

`prob_bad_or_coverage_le_of_caps_recorded` carries `¬ SeedRandomised` — *no cached message input
anywhere has `SK.prf` for its randomiser*. That is a statement about the whole query set, and its
complement costs one unit per query. It cannot be paid: the `q` coefficient of the ledger is
exactly two and both units are spent.

What `SplitWitness.mem_records_of_covered` actually uses the narrowing for is **one input** — the
forgery's own digest — and the weakened cover (`ObligationShapes.cover_of_served_or_narrow`)
leaves nothing else needing it, because a disclosing witness satisfies `served ∨ narrow` by being
served. So the honest leftover is `ForgerySeedRandomised`: *the forgery's published randomiser is
`SK.prf`*. It names one object rather than a query set, which is what makes it statable at the
paired run at all, and the shared half charges it there at `seedUnits` units of `2 ^ -128`
(`ObligationShapes.sharedChargedLate_of_parts`, whose `hclaims : 259 + seedUnits ≤ claims` is what
the ledger's spare constants have to cover).

**It is not one unit, and the earlier version of this paragraph said it was.** The reason that
looked right — a guess at a secret the signer never publishes — is refuted by
`ObligationShapes.publishedRandomizer_eq_truncate`: a signature's randomiser is `Hashing.truncate`
of the oracle's answer at the seed's own `PRF_msg` input, so one signing request turns the secret
into a *testable* quantity, one candidate per query. `ObligationShapes`' section "Why `seedUnits`
is a parameter and not `1`" is that argument. Counting the adversary's outputs is not counting its
chances, and the difference between a leftover that can be charged and one that cannot is what the
event is **quantified over** — not how tight the argument is.

The narrowed join is a hypothesis here and not a step, because proving it is the weakening of
`SplitWitness.Served.mem_records_of_covered` — its `hnarrowCached` cut down from every cached
message input to the forgery's digest alone — which lives in another file. Stated in the shape
that weakening will have, so the two meet by `exact` when it lands. -/

/-- **The narrowing's leftover, at the forgery alone.** The forgery's published randomiser is the
signer's `PRF_msg` seed.

One object, which is what makes it statable at the paired run at all — but **not one unit**. The
randomiser a signature publishes is `Hashing.truncate` of the oracle's answer at the seed's own
`PRF_msg` input (`ObligationShapes.publishedRandomizer_eq_truncate`), so one signing request
makes the seed checkable at one candidate per query. The shared half charges it at `seedUnits`,
not at `1`. -/
def ForgerySeedRandomised (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∃ (message : Bytes) (parsed : Signature),
    result.1.1.forgery.message.frame = some message ∧
      Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
        RandomizerGate.PrfClass prfSeed (Hashing.messageInput parsed.randomizer pk message)

/-- **The forgery's leftover is a case of the cache's.** So the narrowed hypothesis really is
weaker than the one it replaces, and the old join still discharges the new one wherever the
forgery's digest is cached — which `ForgeryCoveredBy` always supplies. -/
theorem seedRandomised_of_forgerySeedRandomised (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hforgery : ForgerySeedRandomised prfSeed pk result)
    (hcached : ∀ (message : Bytes) (parsed : Signature),
      result.1.1.forgery.message.frame = some message →
        Signature.fromBytes? result.1.1.forgery.signature = some parsed →
          result.2 (Hashing.messageInput parsed.randomizer pk message) ≠ none) :
    SplitWitness.SeedRandomised prfSeed pk result.2 := by
  obtain ⟨message, parsed, hframe, hparsed, hprf⟩ := hforgery
  exact ⟨Hashing.messageInput parsed.randomizer pk message, hcached message parsed hframe hparsed,
    ⟨parsed.randomizer, message, rfl⟩, hprf⟩

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges at the recorded run, with the leftover narrowed.** Identical
to `prob_bad_or_coverage_le_of_caps_recorded` except that the coverage clause carries the
forgery-local leftover in place of the cache-wide one, and the join that reads it is a hypothesis
rather than a step. -/
theorem prob_bad_or_coverage_le_of_caps_recorded_narrow (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      SplitWitness.targetKeep prfSeed pk input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hjoinNarrow : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      SplitWitness.CoveredAtKeep prfSeed pk
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
        ¬ ForgerySeedRandomised prfSeed pk
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
        ¬ SplitWitness.LateDisclosure prfSeed pk
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) →
        BlockViews.TargetCovered result)
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad (result.1, result.2.1) ∨
          (SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
            ¬ ForgerySeedRandomised prfSeed pk (result.1, result.2.1) ∧
            ¬ SplitWitness.LateDisclosure prfSeed pk result) |
        BlockViews.recordedRun
          (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
          (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join_recorded inClass hne
    (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
    hrightClass bad hrate hbadClass computation initialCache hclean
    (fun result => SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
      ¬ ForgerySeedRandomised prfSeed pk (result.1, result.2.1) ∧
      ¬ SplitWitness.LateDisclosure prfSeed pk result)
    leftLength budget hcap
    (fun result hmem hcoverage =>
      hjoinNarrow result hmem hcoverage.1 hcoverage.2.1 hcoverage.2.2)
    hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne hrightClass computation
      initialCache result hmem budget hbudget)
    budget hbudget

/-! ## The narrowed join, discharged

`hjoinNarrow` above was stated in the shape the weakening of
`SplitWitness.Served.mem_records_of_covered` would have. The weakening is proved, so the shape is
now a theorem and the hypothesis is closed by `exact` — against one remaining demand,
`Served.WitnessCover`, which is what a serving flag gives and a cache test does not.

Two things are worth separating here, because they were tangled in `hseed` and are not the same.
`NarrowTarget` is the **leftover**: the forgery's randomiser is `SK.prf`, one object, one unit,
the shared half's to charge. `WitnessCover` is a **presentation defect**: the disclosing test is
read at the view in force when a query was answered, while the coverage event reads it at the
end, and nothing reconciles them unless the test is set at the query. Charging the second is not
merely expensive, it is the wrong repair. -/

open scoped Classical in
/-- **The narrowed leftover gives the narrowed class at the forgery.** The message-class half is
free, so what is left is exactly the `PRF_msg` half, which is `ForgerySeedRandomised`. -/
theorem narrowTarget_of_not_forgerySeedRandomised (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × SplitPrefix.SplitState)
    (hforgery : ¬ ForgerySeedRandomised prfSeed pk (result.1, result.2.1)) :
    SplitWitness.Served.NarrowTarget pk (fun probe _ => SplitWitness.narrowClass prfSeed pk probe) result :=
  fun message parsed _ hframe hparsed _ =>
    ⟨⟨parsed.randomizer, message, rfl⟩,
      fun hprf => hforgery ⟨message, parsed, hframe, hparsed, hprf⟩⟩

open scoped Classical in
/-- **The join at the game's tests, with the narrowing at one input.** This is `hjoinNarrow`'s
body; `prob_bad_or_coverage_le_of_caps_recorded_narrow` consumes it verbatim. -/
theorem targetCovered_of_forgeryDisclosedCovered_narrow (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (computation : OracleComp OracleWorld Outcome) (cache : QueryCache HashSpec)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (result : (Outcome × Counts) × SplitPrefix.SplitState)
    (hmem : result ∈ support (BlockViews.recordedRun
      (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
      (countQueries (splitCost inClass inside outside) computation) cache))
    (hcover : SplitWitness.Served.WitnessCover (SplitWitness.disclosingKeep prfSeed pk)
      (SplitWitness.disclosingKeep prfSeed pk)
        (fun probe _ => SplitWitness.narrowClass prfSeed pk probe)
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hcovered : SplitWitness.CoveredAtKeep prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hforgery : ¬ ForgerySeedRandomised prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hlate : ¬ SplitWitness.LateDisclosure prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) :
    BlockViews.TargetCovered result := by
  classical
  obtain ⟨target, htarget, hwitness⟩ :=
    SplitWitness.mem_records_of_covered_of_not_late_narrow prfSeed pk
      (countAllHashes computation) cache
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)
      (mem_support_recorder_countAllHashes (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.targetKeep prfSeed pk) inClass hne computation (cache, [], []) result hmem)
      hfresh hcover
      (narrowTarget_of_not_forgerySeedRandomised prfSeed pk _ hforgery) hlate hcovered
  refine ⟨target, htarget, fun tree => ?_⟩
  obtain ⟨witness, hmember, -, hinstance, hleaf⟩ := hwitness tree
  exact ⟨witness, hmember, hinstance, hleaf⟩

/-! ## And the charge with `hjoinNarrow` discharged

Nothing is left of the narrowing's cost but `WitnessCover`, which is not a charge at all: it says
the disclosing test holds when the query is answered and not merely at the end. A serving flag
gives it outright. So the answer half's remaining debts are now three hypotheses of one kind —
the recorder's test being the signing log (`hdisclosing`), the recording being one entry per
served request (`hleftBound`), and this — and all three are the same statement about the same
object, which is why the carrier settles them together. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges with the narrowed join proved rather than assumed.** -/
theorem prob_bad_or_coverage_le_of_caps_recorded_witnessCover (prfSeed : Digest) (pk : PublicKey)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ (input : Bytes) (cache : QueryCache HashSpec),
      SplitWitness.targetKeep prfSeed pk input cache → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      initialCache input = none)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hwitnessCover : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      SplitWitness.Served.WitnessCover (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.disclosingKeep prfSeed pk)
        (fun probe _ => SplitWitness.narrowClass prfSeed pk probe)
        ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad (result.1, result.2.1) ∨
          (SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
            ¬ ForgerySeedRandomised prfSeed pk (result.1, result.2.1) ∧
            ¬ SplitWitness.LateDisclosure prfSeed pk result) |
        BlockViews.recordedRun
          (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
          (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 :=
  prob_bad_or_coverage_le_of_caps_recorded_narrow prfSeed pk inClass hne hrightClass bad hrate
    hbadClass computation initialCache hclean leftLength hcap
    (fun result hmem hcovered hforgery hlate =>
      targetCovered_of_forgeryDisclosedCovered_narrow prfSeed pk inClass hne computation
        initialCache hfresh result hmem (hwitnessCover result hmem) hcovered hforgery hlate)
    hleftBound budget hbudget

/-! ## The leftover is a bookkeeping gap, and what it would cost to close it

The leftover exists only because `SplitWitness.narrowClass` carries `¬ PrfClass`. Widen the class
to the message class and it vanishes — `narrowTarget_messageClass` below is that, proved, so the
claim is checkable rather than asserted. Everything else on the answer side is already generic in
the two tests, so nothing of this file would move.

**What the widening costs is not what its docstring says.** That docstring says the budget has no
room for one target entry per served request. It has: `BlockViews.prob_targetCovered_le` caps
only the *disclosing* recording (`leftLength ≤ 5 * 2 ^ 62`) and leaves the target recording's
length free, and `rightRecord_length_le_count` charges target entries against the inside slot of
the split counter, which the budget already covers — the signer's randomiser probe is a hash
query and is counted. The extra entries are free.

**What it really costs is a case in the provenance argument.**
`LateProvenance.hrecord_of_signerDigestFree` has to show every target-recorded input is a query
`SharedJoin.recordOf` holds, and it closes the signer's-randomiser-probe case by `¬ PrfClass`
itself. Widen the class and up to `signingLimit` signer probes become target-recorded while the
record holds only the adversary's and the verifier's queries, so that argument fails and the
ordering charge's containment goes with it.

**The repair is the framing, not the class.** `HandlerCarrier.not_filesLeft_randomizerInput`
already excludes the signer's randomiser probe from the *disclosing* recording by comparing
against the frame in flight, and `RecorderView.noticingRecorderOf` now lets a filing test read a
state that has been told about the query. Excluding it from the *target* recording the same way
removes the need for `¬ PrfClass` entirely, and then `NarrowTarget` is `narrowTarget_messageClass`
and the leftover is gone rather than paid. That is the carrier again, and it is the fourth thing
it settles. -/

/-- **At the message class the narrowed demand is no demand at all.** So the leftover is exactly
the `PRF_msg` clause of `SplitWitness.narrowClass` and nothing else; remove the clause and
`NarrowTarget` is discharged by this, with no hypothesis and no charge. -/
theorem narrowTarget_messageClass (pk : PublicKey)
    (result : (Outcome × Nat) × SplitPrefix.SplitState) :
    SplitWitness.Served.NarrowTarget pk (fun probe _ => CombinedCharge.IsMessageInput pk probe) result :=
  fun message parsed _ _ _ _ => ⟨parsed.randomizer, message, rfl⟩

/-! ## The same charge with the narrowed class a parameter

The leftover is `narrowClass`'s `PRF_msg` clause and its retirement is commissioned, so the chain
below leaves the class free and carries `SplitWitness.Served.NarrowTarget` as a **conjunct** of
the charged event rather than naming the leftover.

That is what makes the retirement an instantiation. At `narrowClass` the conjunct is the leftover
— `narrowTarget_of_not_forgerySeedRandomised` turns `¬ ForgerySeedRandomised` into it, so the
chargeable reading is a case of this one. At `CombinedCharge.IsMessageInput` the conjunct is
`narrowTarget_messageClass`, which holds of every result, so it drops by `probEvent_mono` and
nothing is left to charge. Neither reading is a rewrite of the other and a mismatch between them
would fail to elaborate.

`hcover` is `WitnessCover` as before: a presentation demand, not a charge, and the carrier's to
discharge. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The join at the game's tests, with the target class a parameter.** -/
theorem targetCovered_of_forgeryDisclosedCovered_class (prfSeed : Digest) (pk : PublicKey)
    (narrow : Bytes → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (computation : OracleComp OracleWorld Outcome) (cache : QueryCache HashSpec)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → cache input = none)
    (result : (Outcome × Counts) × SplitPrefix.SplitState)
    (hmem : result ∈ support (BlockViews.recordedRun
      (SplitWitness.disclosingKeep prfSeed pk)
      (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
      (countQueries (splitCost inClass inside outside) computation) cache))
    (hcover : SplitWitness.Served.WitnessCover (SplitWitness.disclosingKeep prfSeed pk)
      (SplitWitness.disclosingKeep prfSeed pk) (fun probe _ => narrow probe)
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hcovered : SplitWitness.CoveredAtKeep prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hnarrowTarget : SplitWitness.Served.NarrowTarget pk (fun probe _ => narrow probe)
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hlate : ¬ SplitWitness.LateDisclosure prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) :
    BlockViews.TargetCovered result := by
  classical
  obtain ⟨target, htarget, hwitness⟩ :=
    SplitWitness.mem_records_of_covered_of_not_late_class prfSeed pk narrow
      (countAllHashes computation) cache
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)
      (mem_support_recorder_countAllHashes (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
        inClass hne computation (cache, [], []) result hmem)
      hfresh hcover hnarrowTarget hlate hcovered
  refine ⟨target, htarget, fun tree => ?_⟩
  obtain ⟨witness, hmember, -, hinstance, hleaf⟩ := hwitness tree
  exact ⟨witness, hmember, hinstance, hleaf⟩

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The answer half's two charges, with the narrowed class a parameter.** -/
theorem prob_bad_or_coverage_le_of_caps_recorded_class (prfSeed : Digest) (pk : PublicKey)
    (narrow : Bytes → Prop)
    (inClass : Bytes → Prop) {inside outside : QueryKind} (hne : inside ≠ outside)
    (hrightClass : ∀ input : Bytes, narrow input → inClass input)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hbadClass : ∀ input answer, bad input answer → ¬ inClass input)
    (computation : OracleComp OracleWorld Outcome) (initialCache : QueryCache HashSpec)
    (hclean : GrowthCharge.CleanBad bad initialCache)
    (hfresh : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input →
      initialCache input = none)
    (leftLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hcover : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      SplitWitness.Served.WitnessCover (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.disclosingKeep prfSeed pk) (fun probe _ => narrow probe)
        ((result.1.1, result.1.2 inside + result.1.2 outside), result.2))
    (hleftBound : ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep prfSeed pk)
        (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
        (countQueries (splitCost inClass inside outside) computation) initialCache),
      result.2.2.1.length ≤ leftLength)
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
        GrowthCharge.Bad bad (result.1, result.2.1) ∨
          (SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
            SplitWitness.Served.NarrowTarget pk (fun probe _ => narrow probe) result ∧
            ¬ SplitWitness.LateDisclosure prfSeed pk result) |
        BlockViews.recordedRun (SplitWitness.disclosingKeep prfSeed pk)
          (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
          (countAllHashes computation) initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join_recorded inClass hne
    (SplitWitness.disclosingKeep prfSeed pk)
    (SplitWitness.Served.targetKeep (fun probe _ => narrow probe) (SplitWitness.disclosingKeep prfSeed pk))
    (fun input inner hkeep => hrightClass input hkeep.1) bad hrate hbadClass computation
    initialCache hclean
    (fun result => SplitWitness.CoveredAtKeep prfSeed pk (result.1, result.2.1) ∧
      SplitWitness.Served.NarrowTarget pk (fun probe _ => narrow probe) result ∧
      ¬ SplitWitness.LateDisclosure prfSeed pk result)
    leftLength budget hcap
    (fun result hmem hcoverage =>
      targetCovered_of_forgeryDisclosedCovered_class prfSeed pk narrow inClass hne computation
        initialCache hfresh result hmem (hcover result hmem) hcoverage.1 hcoverage.2.1
        hcoverage.2.2)
    hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne
      (fun input inner hkeep => hrightClass input hkeep.1) computation initialCache result hmem
      budget hbudget)
    budget hbudget

/-! ## The disclosing cap

`hleftBound` says the disclosing recording is short. It is not true that every signer-randomised
entry comes from a served request — an adversary may query `messageInput (truncate (PRF …)) pk M`
itself — but to do that it first needs the `PRF_msg` answer, and acquiring *that* is either the
randomiser defect's own event or a guess at the same unit. So the honest statement is about the
`PRF_msg` class at the real seed, and that class's growth is what the shared half charges.

What is proved here is the game half, a counting argument and nothing else: each disclosing
entry is a *distinct* message input, each distinct message input needs its own `PRF_msg` entry,
so the recording is no longer than the growth in the `PRF_msg` class at the real seed. The
remaining conjunct — that growth being inside the signing limit off the defect — is the shared
half's, where the seed is still random.

The injection runs the other way from how the definition reads. `SignerRandomised` pins the
randomiser to the cached `PRF_msg` answer, so the message determines the whole input; two
distinct disclosing entries therefore have distinct messages, and distinct messages have
distinct `PRF_msg` inputs. -/

open scoped Classical in
/-- One step keeps every cached input cached. -/
theorem step_cache_mono (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range queried × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep) queried).run state))
    (probe : Bytes) (hprobe : state.1 probe ≠ none) : step.2.1 probe ≠ none := by
  classical
  rcases queried with coin | input
  · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hprobe
  · rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨answer, hanswer, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    show answer.2 probe ≠ none
    cases hcached : state.1 input with
    | some value =>
      rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
        Set.mem_singleton_iff] at hanswer
      rw [hanswer]
      exact hprobe
    | none =>
      rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hanswer
      obtain ⟨sampled, -, hpair⟩ := hanswer
      rw [show answer.2 = state.1.cacheQuery input sampled from (Prod.ext_iff.mp hpair).2.symm]
      by_cases hsame : probe = input
      · rw [hsame, QueryCache.cacheQuery_self]
        simp
      · rw [QueryCache.cacheQuery_of_ne state.1 sampled hsame]
        exact hprobe

open scoped Classical in
/-- One step caches the input it answers. -/
theorem step_cache_queried (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (input : Bytes) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range (Sum.inr input) × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep)
      (Sum.inr input)).run state)) : step.2.1 input ≠ none := by
  classical
  rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
  obtain ⟨answer, hanswer, hpure⟩ := hstep
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]
  show answer.2 input ≠ none
  cases hcached : state.1 input with
  | some value =>
    rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
      Set.mem_singleton_iff] at hanswer
    rw [hanswer]
    show state.1 input ≠ none
    rw [hcached]
    simp
  | none =>
    rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hanswer
    obtain ⟨sampled, -, hpair⟩ := hanswer
    rw [show answer.2 = state.1.cacheQuery input sampled from (Prod.ext_iff.mp hpair).2.symm,
      QueryCache.cacheQuery_self]
    simp

open scoped Classical in
/-- One step keeps every disclosing entry's input cached. -/
theorem step_leftRecord_cached (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (queried : OracleWorld.Domain) (state : SplitPrefix.SplitState)
    (step : OracleWorld.Range queried × SplitPrefix.SplitState)
    (hstep : step ∈ support (((SplitPrefix.recorder leftKeep rightKeep) queried).run state))
    (hstart : ∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) :
    ∀ entry ∈ step.2.2.1, step.2.1 entry.1 ≠ none := by
  classical
  rcases queried with coin | input
  · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    exact hstart
  · have hgrow := step_cache_mono leftKeep rightKeep (Sum.inr input) state step hstep
    have hinput := step_cache_queried leftKeep rightKeep input state step hstep
    rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
    obtain ⟨answer, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    intro entry hentry
    rw [hpure] at hentry
    refine (?_ : entry ∈ state.2.1 ∨ entry.1 = input).elim (fun hold => hgrow entry.1
      (hstart entry hold)) (fun hnew => by rw [hnew]; exact hinput)
    revert hentry
    show entry ∈ (SplitPrefix.appended leftKeep rightKeep input state answer.1).1 → _
    rw [SplitPrefix.appended]
    split_ifs with hleft hright
    · intro hentry
      rcases List.mem_append.mp hentry with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (by simpa using congrArg Prod.fst (List.mem_singleton.mp hnew))
    · exact fun hentry => Or.inl hentry
    · exact fun hentry => Or.inl hentry

open scoped Classical in
/-- **Every disclosing entry's input is cached by the end.** -/
theorem leftRecord_cached (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : SplitPrefix.SplitState) (result : α × SplitPrefix.SplitState),
      result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
        computation).run state) →
      (∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) →
      ∀ entry ∈ result.2.2.1, result.2.1 entry.1 ≠ none := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hstart
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hstart
  | query_bind queried next ih =>
    intro state result hmem hstart
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    exact ih step.1 step.2 result hrest
      (step_leftRecord_cached leftKeep rightKeep queried state step hstep hstart)

open scoped Classical in
/-- **The disclosing recording files each input once.** An entry is filed only on a cache miss
and the answer is cached from then on, so no input is filed twice. -/
theorem leftRecord_nodup (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (state : SplitPrefix.SplitState) (result : α × SplitPrefix.SplitState),
      result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
        computation).run state) →
      (∀ entry ∈ state.2.1, state.1 entry.1 ≠ none) →
      (state.2.1.map Prod.fst).Nodup →
      (result.2.2.1.map Prod.fst).Nodup := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state result hmem hcached hnodup
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hnodup
  | query_bind queried next ih =>
    intro state result hmem hcached hnodup
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest
      (step_leftRecord_cached leftKeep rightKeep queried state step hstep hcached) ?_
    rcases queried with coin | input
    · rw [SplitPrefix.recorder_run_inl, mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact hnodup
    · rw [SplitPrefix.recorder_run_inr, mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      show ((SplitPrefix.appended leftKeep rightKeep input state answer.1).1.map
        Prod.fst).Nodup
      rw [SplitPrefix.appended]
      split_ifs with hleft hright
      · rw [List.map_append]
        simp only [List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨hnodup, List.nodup_singleton _, ?_⟩
        intro probe hprobe other hother hsame
        obtain ⟨entry, hentry, hequal⟩ := List.mem_map.mp hprobe
        have hinput : entry.1 = input := by
          rw [hequal, hsame, List.mem_singleton.mp hother]
        exact absurd (hinput ▸ hcached entry hentry) (by rw [hleft.1]; simp)
      · exact hnodup
      · exact hnodup

/-! ### The injection into the `PRF_msg` class -/

open scoped Classical in
/-- The `PRF_msg` input behind a signer-randomised digest input. -/
noncomputable def witnessKey (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes) : Bytes :=
  if h : CacheAvailability.SignerRandomised prfSeed pk cache input then
    Hashing.randomizerInput prfSeed pk.seed h.choose
  else input

open scoped Classical in
/-- What the witness is, when there is one. -/
theorem witnessKey_spec (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) (hsigner : CacheAvailability.SignerRandomised prfSeed pk cache input) :
    ∃ (message : Bytes) (prfAnswer : HashOutput),
      witnessKey prfSeed pk cache input = Hashing.randomizerInput prfSeed pk.seed message ∧
        cache (Hashing.randomizerInput prfSeed pk.seed message) = some prfAnswer ∧
          input = Hashing.messageInput (Hashing.truncate prfAnswer) pk message := by
  classical
  rw [witnessKey, dif_pos hsigner]
  obtain ⟨prfAnswer, hcached, hinput⟩ := hsigner.choose_spec
  exact ⟨hsigner.choose, prfAnswer, rfl, hcached, hinput⟩

open scoped Classical in
/-- The witness is a `PRF_msg` input at the real seed, and it is cached.

Presence only. `witnessKey_spec` above hands back the **answer** and the input it determines,
and is the one to use wherever the cached value has to be related to the witness — which is
most places, since the randomiser the witness carries is that value's truncation. -/
theorem witnessKey_prfClass_cached (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hsigner : CacheAvailability.SignerRandomised prfSeed pk cache input) :
    RandomizerGate.PrfClass prfSeed (witnessKey prfSeed pk cache input) ∧
      cache (witnessKey prfSeed pk cache input) ≠ none := by
  obtain ⟨message, prfAnswer, hkey, hcached, -⟩ :=
    witnessKey_spec prfSeed pk cache input hsigner
  refine ⟨⟨pk.seed, message, hkey⟩, ?_⟩
  rw [hkey, hcached]
  simp

open scoped Classical in
/-- **The witness determines the input.** The randomiser is pinned to the cached `PRF_msg`
answer, so the message determines the whole digest input — which is what makes the disclosing
recording no longer than the `PRF_msg` growth. -/
theorem witnessKey_injective (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (left right : Bytes)
    (hleft : CacheAvailability.SignerRandomised prfSeed pk cache left)
    (hright : CacheAvailability.SignerRandomised prfSeed pk cache right)
    (hkey : witnessKey prfSeed pk cache left = witnessKey prfSeed pk cache right) :
    left = right := by
  obtain ⟨leftMessage, leftAnswer, hleftKey, hleftCached, hleftInput⟩ :=
    witnessKey_spec prfSeed pk cache left hleft
  obtain ⟨rightMessage, rightAnswer, hrightKey, hrightCached, hrightInput⟩ :=
    witnessKey_spec prfSeed pk cache right hright
  rw [hleftKey, hrightKey] at hkey
  obtain ⟨-, -, hmessage⟩ := Hashing.randomizerInput_injective hkey
  rw [hmessage] at hleftCached hleftInput
  rw [hleftCached] at hrightCached
  rw [hleftInput, hrightInput, Option.some_inj.mp hrightCached]

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- **The disclosing recording is no longer than the `PRF_msg` growth at the real seed.** Each
entry is a distinct message input, each needs its own `PRF_msg` entry, and those entries were
not there before the run. -/
theorem leftRecord_length_le_prfGrowth (prfSeed : Digest) (pk : PublicKey)
    (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × SplitPrefix.SplitState)
    (hmem : result ∈ support ((simulateQ (SplitPrefix.recorder leftKeep rightKeep)
      computation).run (cache, [], [])))
    (hsigner : ∀ entry ∈ result.2.2.1,
      CacheAvailability.SignerRandomised prfSeed pk result.2.1 entry.1)
    (hprfFresh : ∀ input : Bytes, RandomizerGate.PrfClass prfSeed input → cache input = none)
    (limit : Nat)
    (hgrowth : ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass prfSeed) cache
      result.2.1 limit) :
    result.2.2.1.length ≤ limit := by
  classical
  have hnodup : (result.2.2.1.map Prod.fst).Nodup :=
    leftRecord_nodup leftKeep rightKeep computation (cache, [], []) result hmem
      (by intro entry hentry; exact absurd hentry (by simp)) (by simp)
  have hkeys := hgrowth
    ((result.2.2.1.map Prod.fst).map (witnessKey prfSeed pk result.2.1))
    (List.Nodup.map_on (fun left hleft right hright hkey => by
      obtain ⟨leftEntry, hleftEntry, hleftValue⟩ := List.mem_map.mp hleft
      obtain ⟨rightEntry, hrightEntry, hrightValue⟩ := List.mem_map.mp hright
      exact witnessKey_injective prfSeed pk result.2.1 left right
        (hleftValue ▸ hsigner leftEntry hleftEntry)
        (hrightValue ▸ hsigner rightEntry hrightEntry) hkey) hnodup)
    (fun key hkey => by
      obtain ⟨input, hinput, hvalue⟩ := List.mem_map.mp hkey
      obtain ⟨entry, hentry, hentryValue⟩ := List.mem_map.mp hinput
      obtain ⟨hclass, hcached⟩ := witnessKey_prfClass_cached prfSeed pk result.2.1 input
        (hentryValue ▸ hsigner entry hentry)
      rw [← hvalue]
      exact ⟨hclass, hprfFresh _ hclass, hcached⟩)
  simpa using hkeys

end SlhDsaSecurity.AnswerCoverage

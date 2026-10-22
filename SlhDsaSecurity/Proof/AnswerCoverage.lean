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
    (hcovered : CoverageRouted.ForgeryDisclosedCovered prfSeed pk
      ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1))
    (hseed : ¬ SplitWitness.SeedRandomised prfSeed pk result.2.1) :
    BlockViews.TargetCovered result := by
  classical
  rcases SplitWitness.mem_records_or_seedRandomised prfSeed pk (countAllHashes computation)
      cache ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)
      (mem_support_recorder_countAllHashes (SplitWitness.disclosingKeep prfSeed pk)
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
          (CoverageRouted.ForgeryDisclosedCovered prfSeed pk result ∧
            ¬ SplitWitness.SeedRandomised prfSeed pk result.2) |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / 2 ^ 141 := by
  classical
  refine prob_bad_or_coverage_le_of_join inClass hne
    (SplitWitness.disclosingKeep prfSeed pk) (SplitWitness.targetKeep prfSeed pk)
    hrightClass bad hrate hbadClass computation initialCache hclean
    (fun result => CoverageRouted.ForgeryDisclosedCovered prfSeed pk result ∧
      ¬ SplitWitness.SeedRandomised prfSeed pk result.2)
    leftLength budget hcap (fun result hmem hcoverage => ?_) hleftBound
    (fun result hmem => rightRecord_length_le_budget _ _ inClass hne hrightClass computation
      initialCache result hmem budget hbudget)
    budget hbudget
  exact targetCovered_of_forgeryDisclosedCovered prfSeed pk inClass hne computation initialCache
    hfresh result hmem (hlate result hmem) hcoverage.1 hcoverage.2

end SlhDsaSecurity.AnswerCoverage

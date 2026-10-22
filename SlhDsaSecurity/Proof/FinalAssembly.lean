import SlhDsaSecurity.Proof.AnswerJoin
import SlhDsaSecurity.Proof.SharedAssembly

/-!
# The target, from the hypotheses that are left

`AnswerJoin` closes the answer obligation from four hypotheses and `SharedAssembly` the shared
one from two. `Obligations.target_of_charges` closes the target from the two obligations. This
file composes all three, which is the only statement that tests whether the three fit.

**It is a seam check, and it is written as one.** Each hypothesis below is copied from the file
that consumes it, in that file's spelling, and the composition is a single application with
nothing in between: no rewriting, no `convert`, no adapter. If a producer's shape and a
consumer's drift apart, this stops elaborating, and it stops at the seam rather than three files
later. The places where one file's output feeds its own next lemma are not covered here, and do
not need to be — the mismatches have all been between owners.

What the statement says, read as a list, is what the proof still rests on:

* `hlate`, `hleftBound`, `hdisclosing`, `hseed` — the answer half's four, at the split recorder's
  run and the walk's key;
* `hinput` — the input half's bullet, at the pair that carries the recordings;
* `hsigner` — that no target-recorded input is a served request's own digest input.

Six, two of which — `hdisclosing` and `hsigner` — retire together when the disclosing test stops
reading the cache and starts reading the handler's flag.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FinalAssembly

open Security CanonicalGraph WarmedGame RoutedSplit Target AnswerSide

set_option maxHeartbeats 1000000 in
/-- **The target, from the six hypotheses that remain.** -/
theorem target_of_producers {inside outside : QueryKind} (hne : inside ≠ outside)
    (hlate : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (AnswerJoin.answerRecordedRun adversary walk),
        ¬ SplitWitness.LateDisclosure walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result)
    (hleftBound : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (AnswerJoin.answerRecordedRun adversary walk),
        result.2.2.1.length ≤ signingLimit)
    (hdisclosing : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (tail adversary walk), ∀ input : Bytes,
        ServedLog.servedLog
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (result.1, result.2) input ↔
          SplitWitness.disclosingKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            input result.2)
    (hseed : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
            SplitWitness.SeedRandomised walk.1.1.2.1
              (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result.2 |
          tail adversary walk] ≤ (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary) :
    HasTotalSecurityBits .strong 127 :=
  Obligations.target_of_charges
    (AnswerJoin.answerCharged_of_parts hne hlate hleftBound hdisclosing hseed)
    (SharedAssembly.sharedCharged_of_parts hinput hsigner)

end SlhDsaSecurity.FinalAssembly

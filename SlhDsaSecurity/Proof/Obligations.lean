import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.SigningFaithful

/-!
# The target at the three named events

`Target.target_of_obligations` takes its three events abstractly, because when it was proved
nobody knew what they would be. They are known now: `RoutedSplit.AnswerBad`,
`RoutedSplit.InputBad` and `ReplayGate.RandomiserBad`. This file instantiates the target at them
and so reduces the whole theorem to three statements about the warmed tail, each of which is one
piece of work rather than a design question.

The split itself is proved, and so is the one thing it asked of the game — that the signing log
holds the signer's own answers — so what the target asks for here is two bounds and nothing
else.

Keeping this file separate from `Target` is deliberate. `Target` is about arithmetic: how the
two halves and the defects fit inside `q / 2 ^ 127`, and it should stay provable without knowing
what the events are. This is where the two meet, and it is the file to read to see what is
outstanding.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Obligations

open Security WarmedGame RoutedSplit ReplayGate Target

/-- The answer half at the warmed tail. -/
def AnswerCharged : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result => AnswerBad ((walk.1, result.1), result.2) | tail adversary walk] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))

/-- The input half, read at the walk and the game together. It defers a secret the walk carries
— the cell table — so it cannot be read at a fixed walk, where that secret is already
determined. The ordering defect is paid inside it, against the same record.

Until the served-disclosure rewrite the shared side also carried the randomiser defect. That
charge is gone: the replay branch closes outright by strong freshness, so no branch reaches it. -/
def SharedCharged : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    Pr[fun pair => GoodWalk pair.1 ∧ InputBad ((pair.1.1, pair.2.1), pair.2.2) |
      Target.pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-! ## The two obligations at a refining tail

Two of the hypotheses the earlier shapes left standing are false. `hseed` is false by a byte
format: the signer's own randomiser query on a request framed as `PK.root ‖ m` *is* a message
input at the secret seed, so the event it bounds is certain on a `1 / 256` slice of key
generation. `hlate` is false because late disclosure happens, which is what it is charged for.

The repair is the same in both cases — stop assuming the event away — and differs only in what
replaces it. The seed leftover narrows to a single guess, at the forgery's own published
randomiser, which the answer side's unspent `2 ^ -126` carries. Late disclosure is **ruled out**
on the answer side and **paid** on the shared side, where the record's message-class part has
the room because the input half's bullet is claims-only.

The defect is a predicate of the recorder's recordings, which a result of `tail` does not carry,
so both obligations are stated at a refining tail — and at *an arbitrary one*, because nothing
below this file can name the presentation. The instantiation is an application, made where the
presentation is defined. -/

/-- The answer half at a refining tail, with its defect term a **parameter**.

The term is a parameter because the half's stated allowance and the half's proved bound are not
the same quantity: `AnswerSide.prob_answerBad_good_le_of_caps_recorded_narrow` concludes
`q / 2 ^ 128 + 1 / 2 ^ 141`, and the `2 ^ -126` beside it is added by a weakening. Reading the
obligation at what is proved is four units of `2 ^ -128` cheaper, and the two readings are this
definition at two arguments rather than two definitions. -/
def AnswerChargedAt {γ : Type} (answerDefect : ℝ≥0∞)
    (fused : Adversary →
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) → ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (late : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × γ) →
      Prop) : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result : γ => AnswerBad ((walk.1, (forget result).1), (forget result).2) ∧
          ¬ late (walk, result) | fused adversary walk] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + answerDefect

/-- The answer half at a refining tail, with late disclosure ruled out rather than assumed. -/
def AnswerChargedLate {γ : Type}
    (fused : Adversary →
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) → ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (late : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × γ) →
      Prop) : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result : γ => AnswerBad ((walk.1, (forget result).1), (forget result).2) ∧
          ¬ late (walk, result) | fused adversary walk] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))

/-- The input half and the ordering defect, paid together at the refined paired run. Their
counts are the two parts of one record, so one budget carries both. -/
def SharedChargedLate {γ : Type} (claims : Nat)
    (fused : Adversary →
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) → ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (late : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × γ) →
      Prop) : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    Pr[fun pair => GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair) |
      Target.pairedFused (fused adversary)] ≤
      ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

end SlhDsaSecurity.Obligations

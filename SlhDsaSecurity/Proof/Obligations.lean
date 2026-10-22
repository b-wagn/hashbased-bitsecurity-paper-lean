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

/-- The input half and the randomiser defect against one budget, read at the walk and the game
together. Both halves defer a secret the walk carries — the cell table and `SK.prf` — so neither
can be read at a fixed walk, where that secret is already determined. -/
def SharedCharged : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    Pr[fun pair => GoodWalk pair.1 ∧
        (InputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
          RandomiserBad ((pair.1.1, pair.2.1), pair.2.2)) | Target.pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The target, from the three statements that are left.** -/
theorem target_of_charges (hanswer : AnswerCharged) (hshared : SharedCharged) :
    HasTotalSecurityBits .strong 127 :=
  Target.target_of_obligations AnswerBad InputBad RandomiserBad
    (fun adversary _ hwalk _ _ hresult hwin =>
      SigningFaithful.cases_of_win_charged adversary hwalk hresult hwin)
    hanswer hshared

end SlhDsaSecurity.Obligations

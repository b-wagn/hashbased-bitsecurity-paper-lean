import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.ReplayGate

/-!
# The target at the three named events

`Target.target_of_obligations` takes its three events abstractly, because when it was proved
nobody knew what they would be. They are known now: `RoutedSplit.AnswerBad`,
`RoutedSplit.InputBad` and `ReplayGate.RandomiserBad`. This file instantiates the target at them
and so reduces the whole theorem to three statements about the warmed tail, each of which is one
piece of work rather than a design question.

The split itself is proved — `ReplayGate.cases_of_win_charged` — so what the target asks for
here is its hypothesis about the game, that the signing log holds the signer's own answers, and
then the two bounds.

Keeping this file separate from `Target` is deliberate. `Target` is about arithmetic: how the
two halves and the defects fit inside `q / 2 ^ 127`, and it should stay provable without knowing
what the events are. This is where the two meet, and it is the file to read to see what is
outstanding.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Obligations

open Security WarmedGame RoutedSplit ReplayGate Target

/-- Every result of the warmed tail has a faithful signing log. -/
def LogFaithfulGame : Prop :=
  ∀ (adversary : Adversary),
    ∀ walk ∈ support graphWalk,
      ∀ result ∈ support (tail adversary walk),
        LogFaithful ((walk.1, result.1), result.2)

/-- The answer half at the warmed tail. -/
def AnswerCharged : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result => AnswerBad ((walk.1, result.1), result.2) | tail adversary walk] ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))

/-- The input half and the randomiser defect against one budget. -/
def SharedCharged : Prop :=
  ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
    ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result => InputBad ((walk.1, result.1), result.2) ∨
          RandomiserBad ((walk.1, result.1), result.2) | tail adversary walk] ≤
        ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The target, from the three statements that are left.** -/
theorem target_of_charges (hlog : LogFaithfulGame) (hanswer : AnswerCharged)
    (hshared : SharedCharged) : HasTotalSecurityBits .strong 127 :=
  Target.target_of_obligations AnswerBad InputBad RandomiserBad
    (fun adversary walk hwalk _ result hresult hwin =>
      cases_of_win_charged adversary hwalk hresult (hlog adversary walk hwalk result hresult) hwin)
    hanswer hshared

end SlhDsaSecurity.Obligations

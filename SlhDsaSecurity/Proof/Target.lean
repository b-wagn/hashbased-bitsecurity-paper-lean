import SlhDsaSecurity.Proof.MainTheorem
import SlhDsaSecurity.Proof.WalkDefects
import SlhDsaSecurity.Proof.Assembly
import SlhDsaSecurity.Proof.KeygenBudget

/-!
# The target, and exactly what is still owed it

This is the end of the proof written before the middle is finished: the theorem that concludes
`Security.HasTotalSecurityBits .strong 127`, taking as hypotheses the things not yet proved and
discharging everything that is. Its purpose is to make the list of remaining obligations a Lean
statement rather than a recollection — if two of them cannot hold together, or if one is about
to be proved in a shape that does not fit, that shows up here rather than at the join.

Everything the walk owes is discharged. A walk whose seeds coincide costs one unit of
`2 ^ -128` and one whose public key encodes an address prefix costs `2 ^ -165`, so the three
charges that carried those as hypotheses may take them from the walk; `WalkDefects` proves both
and `probEvent_le_of_good_walk` applies them together.

The arithmetic is discharged too, and every number in it is concrete. Key generation's
`2 ^ subtreeHeight = 512` calls are reserved on both halves, the forgery's `259` claimed cells
are the input half's excess, and six units of `2 ^ -128` cover the four small defects — the
load cap at `2 ^ -126`, the coverage tape at `2 ^ -141`, the input-format coincidence at
`2 ^ -165` and the seed coincidence at `2 ^ -128`. `259 + 6 ≤ 1024` is the whole of it, and the
margin is `759` units.

The budget's own lower bound is discharged as well. `KeygenBudget.pow_le_of_budget` shows that a
budget an adversary can be run under is at least the `2 ^ subtreeHeight` key generation spends,
which is what makes `q - 2 ^ subtreeHeight` a count of calls rather than a truncation.

What is left is three hypotheses, and the file states them in the shape their provers will state
them:

* `hsplit` — a win on a good walk is one of three events. The extraction reaches this as far as
  `CanonicalSplit.cases_of_win_canonical`; what is missing is the provenance split that turns
  its third branch into a contradiction with strong freshness.
* `hanswer` — the answer half at the warmed tail, with the growth reserved and its two defects.
* `hshared` — the input half and the randomiser defect against **one** budget. They share it
  because their chances are disjoint classes of one record plus the signer's own calls, and the
  per-request terms cancel inside that pathwise inequality rather than after a uniform bound.
  It is stated on the *disjunction* rather than on the sum of the two probabilities, which is
  what a union over the run's own queries proves: a query is one kind of hit or the other, so
  the two events are covered by a single count, and asking for the sum would ask for a bound
  the shared budget does not support.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Target

open Security CanonicalGraph WarmedGame

/-- A walk the three charges can be read against: its two seeds differ, and its public key is
no coincidence. -/
def GoodWalk (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) : Prop :=
  walk.1.1.2.1 ≠ walk.1.1.2.2 ∧
    ¬ HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode))

/-- **Both of the walk's own coincidences, charged together.** -/
theorem prob_bad_walk :
    Pr[fun walk => ¬ GoodWalk walk | graphWalk] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_mono (q := fun walk => walk.1.1.2.1 = walk.1.1.2.2 ∨
    HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)))
    fun walk _ hbad => ?_) ?_
  · by_cases hseeds : walk.1.1.2.1 = walk.1.1.2.2
    · exact Or.inl hseeds
    · exact Or.inr (by_contra fun hpossible => hbad ⟨hseeds, hpossible⟩)
  · exact le_trans (probEvent_or_le _ _ _)
      (add_le_add WalkDefects.prob_prf_eq_publicSeed_walk WalkDefects.prob_possible_walk)

/-- **A bound that holds after every good walk holds for the warmed run**, at the cost of the
walk's own two coincidences. -/
theorem probEvent_le_of_good_walk (adversary : Adversary)
    (event : (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) ×
      QueryCache HashSpec → Prop) (bound : ℝ≥0∞)
    (htail : ∀ walk ∈ support graphWalk, GoodWalk walk →
      Pr[fun result => event ((walk.1, result.1), result.2) | tail adversary walk] ≤ bound) :
    Pr[event | warmedRun adversary] ≤
      bound + (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞)) := by
  classical
  rw [warmedRun_eq, probEvent_map]
  refine le_trans (WalkDefects.probEvent_bind_pair_split_le graphWalk (tail adversary)
    (fun walk result => event ((walk.1, result.1), result.2))
    (fun walk => ¬ GoodWalk walk) bound
    (fun walk hwalk hgood => htail walk hwalk (not_not.mp hgood))) ?_
  exact add_le_add le_rfl prob_bad_walk

/-! ## The allowance

Six units of `2 ^ -128` against the four defects, and `259` claimed cells against the `1024`
that key generation's spend reserves on the two halves. -/

/-- The four small defects, as one quantity. -/
noncomputable def defects : ℝ≥0∞ :=
  (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
    ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞))

/-- **The allowance closes, with every number concrete.** -/
theorem allowance (q : Nat) (hkeygen : 2 ^ subtreeHeight ≤ q) :
    ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defects) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hdefects : defects ≤ ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    rw [defects, show (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞)) =
      (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
        (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) from by
      ring]
    exact Assembly.defects_le_six
  rw [← add_assoc]
  exact Assembly.le_target_of_counts q (2 ^ subtreeHeight) 259 6 hkeygen
    (by simp only [subtreeHeight]; omega) defects hdefects

/-! ## The target -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The target, from three obligations.** Each is stated at the warmed tail, on a walk whose
own coincidences have already been paid for. -/
theorem target_of_obligations
    (answerBad inputBad randomiserBad :
      (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) × QueryCache HashSpec → Prop)
    (hsplit : ∀ (adversary : Adversary), ∀ walk ∈ support graphWalk, GoodWalk walk →
      ∀ result ∈ support (tail adversary walk), Wins .strong result.1.1 →
        answerBad ((walk.1, result.1), result.2) ∨
          inputBad ((walk.1, result.1), result.2) ∨
            randomiserBad ((walk.1, result.1), result.2))
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result => answerBad ((walk.1, result.1), result.2) | tail adversary walk] ≤
          ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
              (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)))
    (hshared : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result => inputBad ((walk.1, result.1), result.2) ∨
            randomiserBad ((walk.1, result.1), result.2) | tail adversary walk] ≤
          ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 := by
  classical
  refine MainTheorem.totalSecurityBits_of_bound
    (fun q => (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) (fun q _ => le_rfl)
    fun q adversary hq hbudget => ?_
  refine le_trans (probEvent_le_of_good_walk adversary
    (fun result => Wins .strong result.1.2.1)
    (((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
          (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)))) ?_) ?_
  · intro walk hwalk hgood
    calc Pr[fun result => Wins .strong result.1.1 | tail adversary walk]
        ≤ Pr[fun result => answerBad ((walk.1, result.1), result.2) ∨
              (inputBad ((walk.1, result.1), result.2) ∨
                randomiserBad ((walk.1, result.1), result.2)) | tail adversary walk] :=
          probEvent_mono fun result hresult hwin =>
            hsplit adversary walk hwalk hgood result hresult hwin
      _ ≤ Pr[fun result => answerBad ((walk.1, result.1), result.2) | tail adversary walk] +
            Pr[fun result => inputBad ((walk.1, result.1), result.2) ∨
              randomiserBad ((walk.1, result.1), result.2) | tail adversary walk] :=
          probEvent_or_le _ _ _
      _ ≤ (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
              ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
                (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))) +
            ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
          add_le_add (hanswer q adversary hq hbudget walk hwalk hgood)
            (hshared q adversary hq hbudget walk hwalk hgood)
      _ = _ := by ring
  · rw [show ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
            (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))) +
        (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞)) =
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defects) from by
      rw [defects]; ring]
    exact allowance q (KeygenBudget.pow_le_of_budget q adversary hbudget)

end SlhDsaSecurity.Target

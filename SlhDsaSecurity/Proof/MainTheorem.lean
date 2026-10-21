import SlhDsaSecurity.Proof.Assembly
import SlhDsaSecurity.Statement.Security
import SlhDsaSecurity.Proof.WholeGameStructural
import SlhDsaSecurity.Proof.WarmedGame

/-!
# The target, reduced to its two halves

Everything proved so far is either a charge — a bound on how much one avenue can be worth per
query — or a piece of the structural reduction that says a forgery has to take one of those
avenues. This file does the last arithmetic step, and it is worth isolating because it is the
only place where the shape of the whole argument is checked against the statement it is
supposed to prove.

`totalSecurityBits_of_halves` says: given a split of the winning event into an answer-side
event and an input-side event, and a bound of `q / 2 ^ 128` on each, the target
`HasTotalSecurityBits .strong 127` follows. The two bounds add to `q / 2 ^ 127` exactly, with
no room to spare — which is the arithmetic fact that has shaped every choice in this
development: the per-class accounting, the joint answer-side charge whose rate is a maximum
rather than a sum, and the exact rather than approximate input-side comparison.

What remains after this file is exactly its three hypotheses, instantiated at the real game:

* `hsplit` — an accepted fresh forgery forces one of the two events. The structural half of
  this is `HypertreeDispatch.cases_of_accepted` together with the five charge compositions and
  `ForsDispatch.deviatingCollision_of_forsCollision`; what is missing is the game-level step
  that unfolds `Scheme.verify` and exhibits the public key as the honest one.
* `hanswer` — `CombinedCharge.prob_combinedBad_within_le` with `ClassBudget.growthOn_le_count`,
  at the cells the experiment's key generation produces.
* `hinput` — `BlindComparison.prob_touched_eq` with `SeedDeferral.prob_run_meets_honest_key_le`,
  at the seed-derived keys of that key generation.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.MainTheorem

open Security

/-! ## The game with its cache kept

`Security.runAll` discards the oracle cache: it is `run'`, which keeps only the value. Every
charge in this development is stated about the run that keeps the cache, because the events it
bounds — `GrowthCharge.Bad`, `StructuralTerm.DeviatingCollision` — are statements about cache
entries.

The two are the same experiment, so an event about the value alone has the same probability
either way. `probEvent_runAll` is that, and it is what lets the three obligations of
`totalSecurityBits_of_halves` be discharged against the charges rather than restated. -/

/-- **An event about the value alone does not see the cache.** The cache-keeping run is
`WholeGameStructural.instrumentedRun`; this says the projection costs nothing. -/
theorem probEvent_runAll (adversary : Adversary) (event : Outcome × Nat → Prop) :
    Pr[event | runAll adversary] =
      Pr[fun result => event result.1 | WholeGameStructural.instrumentedRun adversary] := by
  rw [runAll, XmssSecurity.RandomOracleModel.run, WholeGameStructural.instrumentedRun,
    show (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run' ∅ =
      Prod.fst <$> (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run ∅
      from rfl, probEvent_map]
  rfl

/-- **The target follows from the two halves.** -/
theorem totalSecurityBits_of_halves
    (answerBad inputBad : (Outcome × Nat) × QueryCache HashSpec → Prop)
    (hsplit : ∀ (adversary : Adversary),
      ∀ result ∈ support (WholeGameStructural.instrumentedRun adversary),
      Wins .strong result.1.1 → answerBad result ∨ inputBad result)
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[answerBad | WholeGameStructural.instrumentedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[inputBad | WholeGameStructural.instrumentedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 := by
  intro q hq adversary hbudget
  rw [totalAdvantage, probEvent_runAll adversary (fun result => Wins .strong result.1)]
  calc Pr[fun result : (Outcome × Nat) × QueryCache HashSpec => Wins .strong result.1.1 |
        WholeGameStructural.instrumentedRun adversary]
      ≤ Pr[fun result => answerBad result ∨ inputBad result |
          WholeGameStructural.instrumentedRun adversary] :=
        probEvent_mono (fun result hmem hwin => hsplit adversary result hmem hwin)
    _ ≤ Pr[answerBad | WholeGameStructural.instrumentedRun adversary] +
          Pr[inputBad | WholeGameStructural.instrumentedRun adversary] :=
        probEvent_or_le _ _ _
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        add_le_add (hanswer q adversary hq hbudget) (hinput q adversary hq hbudget)
    _ = (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := Assembly.half_add_half q

/-! ## The halves, at the run that fixes its own cells

`totalSecurityBits_of_halves` asks for two events of the bare game. That is more than can be
supplied: every charge bounds an event against a *fixed* table of honest cells, and in the bare
game the cells are a random variable — a cell drawn after the colliding query would need a
union bound over the whole graph, which the budget cannot pay for.

`WarmedGame.warmedRun` is the same game with the canonical graph walked first. Its value
carries the seeds and the cells, so the two halves may name *this run's* honest key; and by
`WarmedGame.probEvent_warmed` the winning event — which looks only at the outcome — has the
same probability there. This is the form the remaining obligations are stated in. -/

/-- **The target follows from the two halves, at the warmed run.** -/
theorem totalSecurityBits_of_warmed_halves
    (answerBad inputBad :
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × (Outcome × Nat)) ×
        QueryCache HashSpec → Prop)
    (hsplit : ∀ (adversary : Adversary),
      ∀ result ∈ support (WarmedGame.warmedRun adversary),
      Wins .strong result.1.2.1 → answerBad result ∨ inputBad result)
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[answerBad | WarmedGame.warmedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[inputBad | WarmedGame.warmedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 := by
  intro q hq adversary hbudget
  rw [totalAdvantage, probEvent_runAll adversary (fun result => Wins .strong result.1),
    WarmedGame.probEvent_warmed adversary (fun outcome => Wins .strong outcome.1)]
  calc Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary]
      ≤ Pr[fun result => answerBad result ∨ inputBad result |
          WarmedGame.warmedRun adversary] :=
        probEvent_mono (fun result hmem hwin => hsplit adversary result hmem hwin)
    _ ≤ Pr[answerBad | WarmedGame.warmedRun adversary] +
          Pr[inputBad | WarmedGame.warmedRun adversary] := probEvent_or_le _ _ _
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        add_le_add (hanswer q adversary hq hbudget) (hinput q adversary hq hbudget)
    _ = (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := Assembly.half_add_half q

/-! ## The halves with their own allowances

`totalSecurityBits_of_warmed_halves` splits the target down the middle, `q / 2 ^ 128` each.
That is the shape the two halves take when nothing is lost, and it has no room for the small
defects the real charges carry: `2 ^ -141` from the coverage tape's load cap, `2 ^ -126` from
the cap itself, and whatever discharging `HashSeparation.Possible` eventually costs.

The room exists, but not in the arithmetic — it is in the query count. Every hash call in the
game is charged to `q`, key generation's included, and after the graph is walked the honest
phase adds nothing to the cache and can buy nothing on either side. So each half is really
bounded by something below `q / 2 ^ 128`, and the difference pays for the defects.

Rather than fix a shape for that now, the theorem below takes the two allowances as functions
of `q` and asks only that they sum to the target. Where they come from — a count subtracted, a
class separated, a defect parked — is then entirely the business of `Assembly`, which already
has the arithmetic for it. -/

/-- **The target, from any two allowances that sum to it.** -/
theorem totalSecurityBits_of_allowances
    (answerBad inputBad :
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × (Outcome × Nat)) ×
        QueryCache HashSpec → Prop)
    (answerBound inputBound : Nat → ℝ≥0∞)
    (hsum : ∀ q : Nat, 1 ≤ q →
      answerBound q + inputBound q ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞))
    (hsplit : ∀ (adversary : Adversary),
      ∀ result ∈ support (WarmedGame.warmedRun adversary),
      Wins .strong result.1.2.1 → answerBad result ∨ inputBad result)
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[answerBad | WarmedGame.warmedRun adversary] ≤ answerBound q)
    (hinput : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[inputBad | WarmedGame.warmedRun adversary] ≤ inputBound q) :
    HasTotalSecurityBits .strong 127 := by
  intro q hq adversary hbudget
  rw [totalAdvantage, probEvent_runAll adversary (fun result => Wins .strong result.1),
    WarmedGame.probEvent_warmed adversary (fun outcome => Wins .strong outcome.1)]
  calc Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary]
      ≤ Pr[fun result => answerBad result ∨ inputBad result |
          WarmedGame.warmedRun adversary] :=
        probEvent_mono (fun result hmem hwin => hsplit adversary result hmem hwin)
    _ ≤ Pr[answerBad | WarmedGame.warmedRun adversary] +
          Pr[inputBad | WarmedGame.warmedRun adversary] := probEvent_or_le _ _ _
    _ ≤ answerBound q + inputBound q :=
        add_le_add (hanswer q adversary hq hbudget) (hinput q adversary hq hbudget)
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := hsum q hq

/-- The even split is the instance with both allowances at half the target. -/
theorem totalSecurityBits_of_warmed_halves'
    (answerBad inputBad :
      (((Digest × Digest × Digest) × CanonicalGraph.Cells) × (Outcome × Nat)) ×
        QueryCache HashSpec → Prop)
    (hsplit : ∀ (adversary : Adversary),
      ∀ result ∈ support (WarmedGame.warmedRun adversary),
      Wins .strong result.1.2.1 → answerBad result ∨ inputBad result)
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[answerBad | WarmedGame.warmedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[inputBad | WarmedGame.warmedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  totalSecurityBits_of_allowances answerBad inputBad
    (fun q => (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (fun q => (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (fun q _ => le_of_eq (Assembly.half_add_half q)) hsplit hanswer hinput

/-! ## The loosest entry point

`totalSecurityBits_of_allowances` still asks for two *predicates on the warmed run*, and that
is more than the halves can give. The input half's event — a query at a sensitive input — is
not visible in the warmed run's result at all: the walk installed every canonical entry, so
such a query changes nothing in the cache, and it is only observable under the instrumentation
`RecordedQueries` adds. The two halves are therefore bounded in different presentations of the
same game, linked by the transfers already proved.

So the top-level statement should ask for nothing but a bound on the winning event itself,
leaving every split, presentation and transfer below it. That is this. -/

/-- **The target, from any bound on the winning event that stays under it.** -/
theorem totalSecurityBits_of_bound (bound : Nat → ℝ≥0∞)
    (hsum : ∀ q : Nat, 1 ≤ q → bound q ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞))
    (hbound : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[fun result => Wins .strong result.1.2.1 | WarmedGame.warmedRun adversary] ≤ bound q) :
    HasTotalSecurityBits .strong 127 := by
  intro q hq adversary hbudget
  rw [totalAdvantage, probEvent_runAll adversary (fun result => Wins .strong result.1),
    WarmedGame.probEvent_warmed adversary (fun outcome => Wins .strong outcome.1)]
  exact le_trans (hbound q adversary hq hbudget) (hsum q hq)

end SlhDsaSecurity.MainTheorem

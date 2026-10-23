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

**What this file still supplies is `totalSecurityBits_of_bound`**, which `Target` applies
twice. The other five theorems here are earlier shapes of the same step and have no consumers;
`totalSecurityBits_of_halves` in particular is the one the sections below are written around, and
nothing calls it.

`totalSecurityBits_of_halves` says: given a split of the winning event into an answer-side
event and an input-side event, and a bound of `q / 2 ^ 128` on each, the target
`HasTotalSecurityBits .strong 127` follows. The two bounds add to `q / 2 ^ 127` exactly, with
no room to spare — which is the arithmetic fact that has shaped every choice in this
development: the per-class accounting, the joint answer-side charge whose rate is a maximum
rather than a sum, and the exact rather than approximate input-side comparison. The defects had
to go somewhere, and where they went is `Assembly.le_target_of_full`'s single reserve, which is
why the live route runs through `totalSecurityBits_of_bound` instead.

## What actually remains

**Not the three hypotheses below.** The proof is now assembled by
`ObligationShapes.target_of_answer_and_leaves`, and what remains is *its* three:

* `hanswer` — `Obligations.AnswerChargedLate` at `FusedCoverage.fusedTail`, supplied by
  `AnswerShape.answerChargedLate_of_parts`, which reduces it to the disclosing cap, the
  recorder-test/signing-log agreement and the narrowed class at the forgery.
* `hinput` — `SharedAssembly.InputBullet`, the input half's probe containment.
* `hsigner` — `LateProvenance.SignerDigestFree`, in its guarded form.

The three listed below belong to `totalSecurityBits_of_halves` and are kept because the charges
they name are all still live — it is the assembly around them that moved:

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
  rw [runAll, Xmss.RandomOracleModel.run, WholeGameStructural.instrumentedRun,
    show (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run' ∅ =
      Prod.fst <$> (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run ∅
      from rfl, probEvent_map]
  rfl

/-! ## The halves, at the run that fixes its own cells

`totalSecurityBits_of_halves` asks for two events of the bare game. That is more than can be
supplied: every charge bounds an event against a *fixed* table of honest cells, and in the bare
game the cells are a random variable — a cell drawn after the colliding query would need a
union bound over the whole graph, which the budget cannot pay for.

`WarmedGame.warmedRun` is the same game with the canonical graph walked first. Its value
carries the seeds and the cells, so the two halves may name *this run's* honest key; and by
`WarmedGame.probEvent_warmed` the winning event — which looks only at the outcome — has the
same probability there. This is the form the remaining obligations are stated in. -/

/-! ## The halves with their own allowances

`totalSecurityBits_of_warmed_halves` splits the target down the middle, `q / 2 ^ 128` each.
That is the shape the two halves take when nothing is lost, and it has no room for the small
defects the real charges carry.

**The two `2 ^ -1xx` terms are not both load-cap defects, and the naming here is of the
superseded route.** In the live chain the coverage tape's cap costs `2 ^ -141`
(`BlockViews.prob_not_goodBlock_le`, at the `2 ^ 103` cap) and that is the only load-cap defect
spent. The `2 ^ -126` of `ForsConcentrationSharper.uniform_load_tail_sharper_of_le` — the
*sharper* `2 ^ 102` cap's defect — has no live consumer; the `2 ^ -126` that appears in
`Obligations.AnswerChargedLate` and in `Target.defects` is an **allowance the answer half does
not spend**, since `AnswerJoin.answerRecordedBound_class_of_parts` proves
`q / 2 ^ 128 + 1 / 2 ^ 141` and only weakens to the stated right-hand side. Whatever discharging
`HashSeparation.Possible` costs is carried by `Target.prob_bad_walk` instead.

The room exists, but not in the arithmetic — it is in the query count. Every hash call in the
game is charged to `q`, key generation's included, and after the graph is walked the honest
phase adds nothing to the cache and can buy nothing on either side. So each half is really
bounded by something below `q / 2 ^ 128`, and the difference pays for the defects.

Rather than fix a shape for that now, the theorem below takes the two allowances as functions
of `q` and asks only that they sum to the target. Where they come from — a count subtracted, a
class separated, a defect parked — is then entirely the business of `Assembly`, which already
has the arithmetic for it. -/

/-! ## The loosest entry point

`totalSecurityBits_of_allowances` still asks for two *predicates on the warmed run*, and that
is more than the halves can give. The input half's event — a query at a sensitive input — is
not visible in the warmed run's result at all: the walk installed every canonical entry, so
such a query changes nothing in the cache, and it is only observable under the instrumentation
`RecordedQueries` adds. The two halves are therefore bounded in different presentations of the
same game, linked by the transfers already proved.

So the top-level statement should ask for nothing but a bound on the winning event itself,
leaving every split, presentation and transfer below it. That is this. -/

end SlhDsaSecurity.MainTheorem

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

The arithmetic is discharged too, and every number in it is concrete. `allowance` reads
`Assembly.le_target_of_full`, whose content is the `Nat` line `(q - slack + extra) + q +
defectUnits ≤ 2 * q`: key generation's `2 ^ subtreeHeight = 512` calls are the `slack`, the
forgery's `259` claimed cells are the `extra`, and the `defectUnits` cover the small defects —
the coverage tape at `2 ^ -141`, the input-format coincidence at `2 ^ -165`, the seed
coincidence at `2 ^ -128`, and the answer half's own term. So what has to hold is
`claims + defectUnits ≤ 512`. (The `1024` of a `759`-unit margin belongs to
`le_target_of_counts` and `le_target_of_two_slacks`, which reserve on both halves; `allowance`
does not call them.)

**Two readings of the answer half's term, and the margin follows from which is taken.** The
obligation *states* `1 / 2 ^ 126 + 1 / 2 ^ 141`, which is four units plus a sliver, so
`defectUnits` is six and the margin is `247`. The half *proves*
`q / 2 ^ 128 + 1 / 2 ^ 141` — `AnswerSide.prob_answerBad_good_le_of_caps_recorded_narrow` — and
reaches the stated form by `le_add_right`. At what is proved, `defectUnits` is two and the
margin is `251`. `defectsAt` takes the term as a parameter so that both readings are one
statement, and `answerDefectProved` is the second one.

**The `2 ^ -126` here is not the sharper concentration cap's**, which is a different quantity
with no consumer. They are numerically equal, so no arithmetic can tell them apart and the
distinction has to be carried in words: this one is the allowance `Obligations.AnswerChargedLate`
states for the answer half, and the other is a bound in `ForsConcentrationSharper`. Calling this
one "the load cap" is the confusion `MainTheorem`'s narrative had, and it is why nothing caught
it.

The `q` coefficient has no margin at all: the same `Nat` line is `2 * q` on the right and
`q + q` on the left, so the two halves have one budget each and a third `q`-proportional term
cannot be added. Constants can, up to the margin, which is why `allowanceAt` takes the claims
numeral and the defect units as parameters.

**What is still open is five propositions, not two obligations, and they are not five
independent pieces of work.** The fused target takes an answer obligation and a shared one, and
each decomposes. The answer side's three are `Served.WitnessCover`, `hleftBound` and
`hdisclosing` — `hjoinNarrow` is *not* among them, because
`AnswerCoverage.targetCovered_of_forgeryDisclosedCovered_narrow` discharges it from
`WitnessCover`, its freshness side condition coming free from `GoodWalk` through
`AnswerSide.not_possible_generatedKey` and `CoverageTail.walk_cache_fresh`. The shared side's two
are the input half's bullet (`InputBullet.ClaimsCharged`) and the seed charge at `seedUnits`.

**Two of the answer side's three are false where they are currently stated, and that is the
honest shape of the remaining work.** All three read disclosure at
`SplitWitness.disclosingKeep`, which is `CacheAvailability.SignerRandomised` — a test on the
cache. `hdisclosing` asks it to be equivalent to the signing log, and
`ServedBridge`'s right-to-left direction is false: an adversary holding `SK.prf` makes the cache
test true with no request behind it. `hleftBound` caps that same recording by `signingLimit`,
and the same adversary overruns the cap. They retire not by being proved but by the recorder's
test becoming the carrier's served one, which is also what gives `WitnessCover` outright. So the
count is **two charges and one presentation move**, and only the two charges are probability
bounds anybody owes.

The arithmetic side conditions are not among the open set. At `claims := 510` and
`seedUnits := 251` both `259 + seedUnits ≤ claims` and `claims + 2 ≤ 2 ^ subtreeHeight` close by
`omega` and `decide`, and the `inside ≠ outside` the split counter takes closes by `decide`.
Counting the signature's hypotheses misstates what is unproved in both directions at once.

**What may be charged as a constant, and what may not.** An event whose witness is a single
object of the run — the forgery, its randomiser, its claims — is not thereby a constant. What
decides it is whether a candidate witness can be *checked* against something the game publishes:
a guess at a secret costs one unit only when a wrong guess cannot be told from a right one. A
signature publishes `Hashing.truncate` of the oracle's answer at a seed-derived input, so `SK.prf`
is checkable at one query per candidate; an authentication path publishes the hash of a secret the
signature did not reveal, so that secret is checkable too. In both cases the adversary's chances
are its queries and not its outputs, and a charge that counts the outputs is wrong by a factor of
`q`.

So the constants here are exactly the events nobody can check: the walk's own two coincidences,
drawn before any adversary exists and never compared against anything, and the two tape bounds,
which are concentration and not guessing. Every other charge in the development counts the
queries — and that is what makes it safe, because a test *is* a query and pays for itself.

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

/-! ## The walk and the game together

A charge whose secret is *in the walk* cannot be read at a fixed walk. Conditioning on the walk
fixes `SK.prf` and the cell table, and an adversary may have been chosen knowing them — for the
walk whose `SK.prf` is the constant it hardcodes, the event it is charged for happens with
probability one. Every deferral in this development draws its secret after the run, and that is
not available once the walk is a parameter.

So the obligations that defer a secret are stated *here*, on the walk and the game taken
together, where the walk's own randomness is still in the measure. The answer side is unaffected
and stays at a fixed walk: its charges are guesses at the tail's own fresh answers, which no
choice of adversary can bias in advance. -/

/-- The walk and the game that follows it, with the walk's value retained. -/
noncomputable def pairedRun (adversary : Adversary) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) := do
  let walk ← graphWalk
  let result ← tail adversary walk
  pure (walk, result)

/-- **The walk's own coincidences, read at the paired run.** -/
theorem prob_bad_walk_paired (adversary : Adversary) :
    Pr[fun pair => ¬ GoodWalk pair.1 | pairedRun adversary] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (WalkDefects.probEvent_bind_pair_split_le graphWalk (tail adversary)
    (fun walk _ => ¬ GoodWalk walk) (fun walk => ¬ GoodWalk walk) 0
    fun walk _ hgood => ?_) ?_
  · rw [show (fun _ : (Outcome × Nat) × QueryCache HashSpec => ¬ GoodWalk walk) =
      fun _ => False from by funext _; simp [not_not.mp hgood]]
    simp
  · rw [zero_add]
    exact prob_bad_walk

/-! ## The allowance

Six units of `2 ^ -128` against the four defects, and `claims` cells against the `512` that key
generation's spend reserves. `allowanceOf` calls `Assembly.le_target_of_full`, which reserves on
**one** half — the answer half is charged the whole `q` — so the budget is `2 ^ subtreeHeight`
and not twice it, and `hclaims` is `claims + 6 ≤ 512`. At the live `claims = 259` the margin is
`247`. (A `1024` belongs to `Assembly.le_target_of_counts`, which reserves on both halves and
which `allowanceOf` does not call.) -/

/-- The four small defects, as one quantity. -/
noncomputable def defects : ℝ≥0∞ :=
  (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
    ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞))

/-- The small defects, with the **answer half's own term a parameter**. The other two are the
walk's, and the walk pays them whatever the answer half's bound turns out to be. -/
noncomputable def defectsAt (answerDefect : ℝ≥0∞) : ℝ≥0∞ :=
  answerDefect +
    ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞))

theorem defects_eq_defectsAt :
    defects = defectsAt ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
      (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)) := rfl

/-- **The answer half's defect term, at what the answer half proves.**

`AnswerSide.prob_answerBad_good_le_of_caps_recorded_narrow` concludes `q / 2 ^ 128 + 1 / 2 ^ 141`,
and `AnswerJoin` adds the `2 ^ -126` to it by `le_add_right` alone — only so that the bound
matches the obligation's stated right-hand side. So the `2 ^ -126` is an allowance that route
does not spend, and reading the answer half at what it proves frees four units of `2 ^ -128`.

**It is not the same `2 ^ -126` as the sharper concentration cap's**, which also has no consumer.
Those two quantities are equal and unrelated, and arithmetic cannot tell them apart, so the
distinction has to be kept in words: this one is the allowance `AnswerChargedLate` states, and
the other is a bound in `ForsConcentrationSharper`. -/
noncomputable def answerDefectProved : ℝ≥0∞ := (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)

private theorem castPow (k : Nat) : ((2 ^ k : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ k := by
  push_cast; ring

private theorem divPowEq (m j k : Nat) (hjk : j ≤ k) :
    ((m : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ j =
      ((m * 2 ^ (k - j) : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ k := by
  have hsplit : (2 : ℝ≥0∞) ^ k = (2 : ℝ≥0∞) ^ (k - j) * (2 : ℝ≥0∞) ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hnum : ((m * 2 ^ (k - j) : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (k - j) * (m : ℝ≥0∞) := by
    push_cast; ring
  rw [hsplit, hnum, ENNReal.mul_div_mul_left _ _ (by positivity) (by simp)]

/-- **Three small defects cost under two units of `2 ^ -128`.** The companion of
`Assembly.defects_le_six` with the answer half's unspent allowance left out. The two helpers
above are `Assembly`'s own, which are `private` there. -/
theorem defectsAt_proved_le_two :
    defectsAt answerDefectProved ≤ ((2 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [defectsAt, answerDefectProved, castPow, castPow, castPow,
    show (1 : ℝ≥0∞) = ((1 : Nat) : ℝ≥0∞) from by push_cast; ring,
    divPowEq 1 141 165 (by norm_num), divPowEq 1 165 165 (by norm_num),
    divPowEq 1 128 165 (by norm_num), divPowEq 2 128 165 (by norm_num),
    ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  rw [← Nat.cast_add, ← Nat.cast_add]
  refine ENNReal.div_le_div_right ?_ _
  exact Nat.cast_le.mpr (by norm_num)

/-- **The allowance closes, at any answer-half defect term and any number of claimed cells.**
The two numerals it takes are tied together by `hclaims`: what the forgery claims and what the
defects cost share the `2 ^ subtreeHeight` key generation reserves. -/
theorem allowanceAt (answerDefect : ℝ≥0∞) (claims defectUnits q : Nat)
    (hdefect : defectsAt answerDefect ≤ ((defectUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hclaims : claims + defectUnits ≤ 2 ^ subtreeHeight) (hkeygen : 2 ^ subtreeHeight ≤ q) :
    ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defectsAt answerDefect) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [← add_assoc]
  exact Assembly.le_target_of_full q (2 ^ subtreeHeight) claims defectUnits hkeygen hclaims
    (defectsAt answerDefect) hdefect

/-- **The allowance closes, at any number of claimed cells key generation's spend leaves room
for.** The numeral is a parameter because the shared side's constant term is not settled: what
the forgery claims is `259`, and anything else charged as a constant lands beside it and has to
fit in the same `2 ^ subtreeHeight` that key generation reserves, alongside the six units the
four small defects take. -/
theorem defects_le_six_units : defects ≤ ((6 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [defects, show (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
      (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
      ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞)) =
    (1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞) +
      (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) from by
    ring]
  exact Assembly.defects_le_six

theorem allowanceOf (claims q : Nat) (hclaims : claims + 6 ≤ 2 ^ subtreeHeight)
    (hkeygen : 2 ^ subtreeHeight ≤ q) :
    ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defects) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [defects_eq_defectsAt]
  exact allowanceAt _ claims 6 q (by rw [← defects_eq_defectsAt]; exact defects_le_six_units)
    hclaims hkeygen

/-- **The allowance at the claims the forgery makes**, which is what the obligations stated
before the numeral was a parameter and what `target_of_obligations` still reads. -/
theorem allowance (q : Nat) (hkeygen : 2 ^ subtreeHeight ≤ q) :
    ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defects) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  allowanceOf 259 q (by simp only [subtreeHeight]; omega) hkeygen

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
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
              (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)))
    (hshared : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[fun pair => GoodWalk pair.1 ∧
          (inputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
            randomiserBad ((pair.1.1, pair.2.1), pair.2.2)) | pairedRun adversary] ≤
        ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 := by
  classical
  refine MainTheorem.totalSecurityBits_of_bound
    (fun q => (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) (fun q _ => le_rfl)
    fun q adversary hq hbudget => ?_
  rw [WarmedGame.warmedRun_eq, probEvent_map]
  have hgoodAnswer :
      Pr[fun pair => GoodWalk pair.1 ∧ answerBad ((pair.1.1, pair.2.1), pair.2.2) |
        pairedRun adversary] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
            (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)) := by
    refine Averaging.probEvent_bind_pair_le graphWalk (tail adversary)
      (fun walk result => GoodWalk walk ∧ answerBad ((walk.1, result.1), result.2)) _
      fun walk hwalk => ?_
    by_cases hgood : GoodWalk walk
    · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
        (hanswer q adversary hq hbudget walk hwalk hgood)
    · rw [show (fun result : (Outcome × Nat) × QueryCache HashSpec =>
        GoodWalk walk ∧ answerBad ((walk.1, result.1), result.2)) = fun _ => False from by
        funext _; simp [hgood]]
      simp
  calc Pr[fun pair : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
        ((Outcome × Nat) × QueryCache HashSpec) =>
        Wins .strong (((pair.1.1, pair.2.1), pair.2.2) : (((Digest × Digest × Digest) × Cells) ×
          (Outcome × Nat)) × QueryCache HashSpec).1.2.1 | pairedRun adversary]
      ≤ Pr[fun pair => (GoodWalk pair.1 ∧ answerBad ((pair.1.1, pair.2.1), pair.2.2)) ∨
            ((GoodWalk pair.1 ∧ (inputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
              randomiserBad ((pair.1.1, pair.2.1), pair.2.2))) ∨ ¬ GoodWalk pair.1) |
          pairedRun adversary] := by
        refine probEvent_mono fun pair hpair hwin => ?_
        by_cases hgood : GoodWalk pair.1
        · obtain ⟨walk, hwalk, result, hresult, hpair⟩ : ∃ walk ∈ support graphWalk,
              ∃ result ∈ support (tail adversary walk), (walk, result) = pair := by
            simpa [pairedRun, eq_comm] using hpair
          subst hpair
          rcases hsplit adversary walk hwalk hgood result hresult hwin with
            hanswerBad | hinputBad | hrandomiserBad
          · exact Or.inl ⟨hgood, hanswerBad⟩
          · exact Or.inr (Or.inl ⟨hgood, Or.inl hinputBad⟩)
          · exact Or.inr (Or.inl ⟨hgood, Or.inr hrandomiserBad⟩)
        · exact Or.inr (Or.inr hgood)
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧ answerBad ((pair.1.1, pair.2.1), pair.2.2) |
            pairedRun adversary] +
          Pr[fun pair => (GoodWalk pair.1 ∧ (inputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
            randomiserBad ((pair.1.1, pair.2.1), pair.2.2))) ∨ ¬ GoodWalk pair.1 |
            pairedRun adversary] := probEvent_or_le _ _ _
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧ answerBad ((pair.1.1, pair.2.1), pair.2.2) |
            pairedRun adversary] +
          (Pr[fun pair => GoodWalk pair.1 ∧ (inputBad ((pair.1.1, pair.2.1), pair.2.2) ∨
              randomiserBad ((pair.1.1, pair.2.1), pair.2.2)) | pairedRun adversary] +
            Pr[fun pair => ¬ GoodWalk pair.1 | pairedRun adversary]) :=
        add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
              (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))) +
          (((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) :=
        add_le_add hgoodAnswer
          (add_le_add (hshared q adversary hq hbudget) (prob_bad_walk_paired adversary))
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defects) := by rw [defects]; ring
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        allowance q (KeygenBudget.pow_le_of_budget q adversary hbudget)

/-! ## The same, at a tail that carries more than the game's result

One of the answer side's events is not a predicate of the game's result at all: late disclosure
says which of the recorder's two recordings an entry was filed on, and a result of `tail` carries
no recordings. So the target is restated here at an arbitrary tail that *refines* the game's —
any `fused` whose results forget to `tail`'s — with the forgetting map a parameter and the one
equation it has to satisfy a hypothesis.

Nothing about the presentation enters: the type is free, the map is free, and what makes the
restatement sound is `hforget` alone, an equality of computations. The numbers are the same
numbers, by `allowance`, and the walk's own two coincidences are paid inside the refined paired
run exactly as they are inside the plain one.

The events split the same way they always did, except that the answer side's now carries
`¬ late` — the defect is *ruled out* there and *paid* on the shared side, instead of being
assumed away on both. -/

/-- The walk and a refining tail played from it. -/
noncomputable def pairedFused {γ : Type}
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) × γ) := do
  let walk ← graphWalk
  let result ← fused walk
  pure (walk, result)

/-- **The walk's own coincidences, read at the refined paired run.** -/
theorem prob_bad_walk_pairedFused {γ : Type}
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ) :
    Pr[fun pair => ¬ GoodWalk pair.1 | pairedFused fused] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (WalkDefects.probEvent_bind_pair_split_le graphWalk fused
    (fun walk _ => ¬ GoodWalk walk) (fun walk => ¬ GoodWalk walk) 0
    fun walk _ hgood => ?_) ?_
  · rw [show (fun _ : γ => ¬ GoodWalk walk) = fun _ => False from by
      funext _; simp [not_not.mp hgood]]
    simp
  · rw [zero_add]
    exact prob_bad_walk

/-- **The refined paired run forgets to the plain one.** -/
theorem pairedRun_eq_map_pairedFused {γ : Type} (adversary : Adversary)
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (hforget : ∀ walk, forget <$> fused walk = tail adversary walk) :
    pairedRun adversary = (fun pair => (pair.1, forget pair.2)) <$> pairedFused fused := by
  rw [pairedRun, pairedFused, map_bind]
  refine bind_congr fun walk => ?_
  rw [← hforget walk, map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, bind_assoc]
  exact bind_congr fun result => by rw [pure_bind]; rfl

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **The target, from two obligations at a refining tail.** The answer side rules the defect
out, the shared side pays for it, and the walk's own coincidences are paid once beside them. -/
theorem target_of_obligations_fused_at {γ : Type} (answerDefect : ℝ≥0∞)
    (claims defectUnits : Nat)
    (hdefect : defectsAt answerDefect ≤ ((defectUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hclaims : claims + defectUnits ≤ 2 ^ subtreeHeight)
    (fused : Adversary → (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) →
      ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (hforget : ∀ (adversary : Adversary) (walk : (((Digest × Digest × Digest) × Cells) ×
      QueryCache HashSpec)), forget <$> fused adversary walk = tail adversary walk)
    (answerBad inputBad :
      (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) × QueryCache HashSpec → Prop)
    (late : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) × γ) → Prop)
    (hsplit : ∀ (adversary : Adversary), ∀ walk ∈ support graphWalk, GoodWalk walk →
      ∀ result ∈ support (tail adversary walk), Wins .strong result.1.1 →
        answerBad ((walk.1, result.1), result.2) ∨ inputBad ((walk.1, result.1), result.2))
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : γ =>
            answerBad ((walk.1, (forget result).1), (forget result).2) ∧
              ¬ late (walk, result) | fused adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + answerDefect)
    (hshared : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[fun pair => GoodWalk pair.1 ∧
          (inputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair) |
        pairedFused (fused adversary)] ≤
        ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 := by
  classical
  refine MainTheorem.totalSecurityBits_of_bound
    (fun q => (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞)) (fun q _ => le_rfl)
    fun q adversary hq hbudget => ?_
  rw [WarmedGame.warmedRun_eq, probEvent_map,
    show (do let walk ← graphWalk; let result ← tail adversary walk; pure (walk, result)) =
      pairedRun adversary from rfl,
    pairedRun_eq_map_pairedFused adversary (fused adversary) forget (hforget adversary),
    probEvent_map]
  have hgoodAnswer :
      Pr[fun pair => GoodWalk pair.1 ∧
          answerBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∧ ¬ late pair |
        pairedFused (fused adversary)] ≤
        (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + answerDefect := by
    refine Averaging.probEvent_bind_pair_le graphWalk (fused adversary)
      (fun walk result => GoodWalk walk ∧
        answerBad ((walk.1, (forget result).1), (forget result).2) ∧ ¬ late (walk, result)) _
      fun walk hwalk => ?_
    by_cases hgood : GoodWalk walk
    · exact le_trans (probEvent_mono fun result _ hbad => hbad.2)
        (hanswer q adversary hq hbudget walk hwalk hgood)
    · rw [show (fun result : γ => GoodWalk walk ∧
        answerBad ((walk.1, (forget result).1), (forget result).2) ∧
          ¬ late (walk, result)) = fun _ => False from by funext _; simp [hgood]]
      simp
  calc Pr[fun pair => Wins .strong (forget pair.2).1.1 | pairedFused (fused adversary)]
      ≤ Pr[fun pair => (GoodWalk pair.1 ∧
            answerBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∧ ¬ late pair) ∨
          ((GoodWalk pair.1 ∧
            (inputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair)) ∨
              ¬ GoodWalk pair.1) | pairedFused (fused adversary)] := by
        refine probEvent_mono fun pair hpair hwin => ?_
        by_cases hgood : GoodWalk pair.1
        · obtain ⟨walk, hwalk, result, hresult, hpair⟩ : ∃ walk ∈ support graphWalk,
              ∃ result ∈ support (fused adversary walk), (walk, result) = pair := by
            simpa [pairedFused, eq_comm] using hpair
          subst hpair
          have hforgetMem : forget result ∈ support (tail adversary walk) := by
            rw [← hforget adversary walk, support_map]
            exact ⟨result, hresult, rfl⟩
          by_cases hlate : late (walk, result)
          · exact Or.inr (Or.inl ⟨hgood, Or.inr hlate⟩)
          · rcases hsplit adversary walk hwalk hgood (forget result) hforgetMem hwin with
              hanswerBad | hinputBad
            · exact Or.inl ⟨hgood, hanswerBad, hlate⟩
            · exact Or.inr (Or.inl ⟨hgood, Or.inl hinputBad⟩)
        · exact Or.inr (Or.inr hgood)
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧
            answerBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∧ ¬ late pair |
            pairedFused (fused adversary)] +
          Pr[fun pair => (GoodWalk pair.1 ∧
            (inputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair)) ∨
              ¬ GoodWalk pair.1 | pairedFused (fused adversary)] := probEvent_or_le _ _ _
    _ ≤ Pr[fun pair => GoodWalk pair.1 ∧
            answerBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∧ ¬ late pair |
            pairedFused (fused adversary)] +
          (Pr[fun pair => GoodWalk pair.1 ∧
              (inputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair) |
              pairedFused (fused adversary)] +
            Pr[fun pair => ¬ GoodWalk pair.1 | pairedFused (fused adversary)]) :=
        add_le_add le_rfl (probEvent_or_le _ _ _)
    _ ≤ ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + answerDefect) +
          (((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞))) :=
        add_le_add hgoodAnswer
          (add_le_add (hshared q adversary hq hbudget)
            (prob_bad_walk_pairedFused (fused adversary)))
    _ = ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + defectsAt answerDefect) := by
        rw [defectsAt]; ring
    _ ≤ (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        allowanceAt answerDefect claims defectUnits q hdefect hclaims
          (KeygenBudget.pow_le_of_budget q adversary hbudget)

/-- **The target at the answer half's stated allowance**, which is the reading the obligations
were written at and the one the dead ledgers below still use. `target_of_obligations_fused_at`
at the term the answer half *proves* is four units cheaper. -/
theorem target_of_obligations_fused {γ : Type} (claims : Nat)
    (hclaims : claims + 6 ≤ 2 ^ subtreeHeight)
    (fused : Adversary → (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) →
      ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (hforget : ∀ (adversary : Adversary) (walk : (((Digest × Digest × Digest) × Cells) ×
      QueryCache HashSpec)), forget <$> fused adversary walk = tail adversary walk)
    (answerBad inputBad :
      (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) × QueryCache HashSpec → Prop)
    (late : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) × γ) → Prop)
    (hsplit : ∀ (adversary : Adversary), ∀ walk ∈ support graphWalk, GoodWalk walk →
      ∀ result ∈ support (tail adversary walk), Wins .strong result.1.1 →
        answerBad ((walk.1, result.1), result.2) ∨ inputBad ((walk.1, result.1), result.2))
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : γ =>
            answerBad ((walk.1, (forget result).1), (forget result).2) ∧
              ¬ late (walk, result) | fused adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) +
              (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞)))
    (hshared : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      Pr[fun pair => GoodWalk pair.1 ∧
          (inputBad ((pair.1.1, (forget pair.2).1), (forget pair.2).2) ∨ late pair) |
        pairedFused (fused adversary)] ≤
        ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  target_of_obligations_fused_at
    ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))
    claims 6 (by rw [← defects_eq_defectsAt]; exact defects_le_six_units) hclaims
    fused forget hforget answerBad inputBad late hsplit hanswer hshared

end SlhDsaSecurity.Target

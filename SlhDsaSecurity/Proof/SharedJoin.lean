import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassExpectation
import SlhDsaSecurity.Proof.ClassGrowth

/-!
# The shared side's charges, added

`Obligations.SharedCharged` is one bound on `InputBad ∨ RandomiserBad`, and several charges pay
for it. This file is the join: each taken in the shape its owner produces, added, and discharged
against `(q - 2 ^ subtreeHeight + 259) / 2 ^ 128`.

**It is stated at `RandomiserRecord.recordedPairedRun`, the walk and the game with the record
retained**, and that is forced rather than convenient. Three of the charges read only the trace;
the randomiser's does not — `RecordMeetsPrfClass` reads the record, and the record is not a
function of the trace, since the cache keeps neither multiplicity nor caller. The only
trace-level version is an existential over records, which this file's own reasoning rules out as
near-vacuous. Nothing is paid for the change: `RandomiserRecord.pairedRun_eq_map` is an equality
of computations, so `probEvent_pairedRun_eq` moves every trace-level event across exactly, and
`InputBad`, `RandomiserBad` and the ordering defect's event all factor through `forgetRecord`
unchanged.

**What the charges are, at the split that exists.** A deferral reads its count off the run
*before* the secret is drawn, so the randomiser defect's count has to be **prf-free** and the
three-way classification of the record by first block is not available to it — two of those
parts name `SK.prf`. What is available is `canonical ⊎ offCanonical`: the record's entries that
are canonical inputs of the walk's own cells, and the rest, which names only the walk. So:

* the input half pays the canonical part, plus the forgery's own 259 claims;
* the randomiser defect pays the off-canonical part;
* the ordering defect pays its own count, which under this split is **not** a share of the
  record — the three-way split that made it one is gone;
* the signer's coincidence pays twice the served requests.

The first two partition the record and the last is disjoint from both. The ordering defect's is
the term that no longer has a home in the partition, and the sum below takes it as a fourth
count without claiming otherwise.

**The counts have to be expectations, and that is the one thing the join forces.** Each charge
would naturally be stated at a *cap* — a constant `L` with the count at most `L` on every
supported run. Caps cannot be added: the partition holds **per run**, and the split between
`work` and `served` is a property of the run, so an almost-sure cap for each count has to cover
its own worst run and four worst-case caps are four budgets. Expectations add where caps do not,
because they add pathwise (`ClassExpectation.expected_add`, `expected_le_of_le`). That is the
move the answer side already made for its coverage term, and
`ClassExpectation.add_le_of_shared_budget` is its two-term form.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharedJoin

open Security WarmedGame RoutedSplit ReplayGate Target RandomiserProvenance RandomiserRecord
  ClassExpectation

/-- What the shared side's events were stated on before the record had to be kept. -/
abbrev Pair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    ((Outcome × Nat) × QueryCache HashSpec)

/-- What they are stated on now: the same, with the run's own record retained. -/
abbrev RecordedPair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)

/-- The trace the shared side's events read, assembled from a paired run's value. -/
abbrev traceOf (pair : Pair) : RoutedSplit.Trace := ((pair.1.1, pair.2.1), pair.2.2)

/-- The same, read off a recorded pair by forgetting its record. -/
abbrev recordedTraceOf (pair : RecordedPair) : RoutedSplit.Trace :=
  traceOf (forgetRecord pair)

/-- The signer's coincidence, conditioned onto the branch the record's charge does not cover.
Both halves are now concrete: the condition is the complement of the randomiser defect's own
event, so nothing is left for a caller to choose. -/
def SignerEvent (pair : RecordedPair) : Prop :=
  SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.1.signed ∧
    ¬ RecordMeetsPrfClass pair.1.1.1.2.1 pair.2

/-! ## The union bound

The shared event is covered by the four, and this is the only step that knows which event is
which. Everything after it is arithmetic on the counts.

The randomiser defect's half of it is no longer a hypothesis: `RandomiserRecord.randomiserBad_dichotomy`
proves it at this presentation, with the record a value of the run rather than a witness. -/

/-- **The shared event is covered by the four.** -/
theorem prob_sharedBad_le_sum (adversary : Adversary) (ordering : RecordedPair → Prop) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
          ¬ ordering pair | recordedPairedRun adversary] +
        Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering pair |
          recordedPairedRun adversary] +
        (Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
              RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 | recordedPairedRun adversary] +
          Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ SignerEvent pair |
            recordedPairedRun adversary]) := by
  classical
  rw [probEvent_pairedRun_eq]
  refine le_trans (probEvent_mono (q := fun pair : RecordedPair =>
    ((GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧ ¬ ordering pair) ∨
        (GoodWalk pair.1 ∧ ordering pair)) ∨
      ((GoodWalk pair.1 ∧ RecordMeetsPrfClass pair.1.1.1.2.1 pair.2) ∨
        (GoodWalk pair.1 ∧ SignerEvent pair))) ?_) ?_
  · rintro pair hpair ⟨hgood, hinputBad | hrandomiserBad⟩
    · by_cases hord : ordering pair
      · exact Or.inl (Or.inr ⟨hgood, hord⟩)
      · exact Or.inl (Or.inl ⟨hgood, hinputBad, hord⟩)
    · by_cases hrec : RecordMeetsPrfClass pair.1.1.1.2.1 pair.2
      · exact Or.inr (Or.inl ⟨hgood, hrec⟩)
      · refine Or.inr (Or.inr ⟨hgood, ?_, hrec⟩)
        exact (randomiserBad_dichotomy adversary pair hpair hgood hrandomiserBad).resolve_left hrec
  · refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ ?_)
    · exact probEvent_or_le _ _ _
    · exact probEvent_or_le _ _ _

/-- The rearrangement the four-term sum needs, at abstract summands so that it stays cheap. -/
theorem add_rearrange (a m p s c : ℝ≥0∞) : a + c + m + (p + s) = a + m + p + s + c := by
  ring

/-! ## The join, at expectations

The four counts are read off the recorded paired run, and the only thing asked of them is that
they stay inside the budget **on every supported run**. `ClassExpectation.expected_add` then
makes the four expectations add to the expectation of the sum, and `expected_le_of_le` bounds
that by the budget. No charge is bounded on its own. -/

set_option maxRecDepth 4000 in
/-- **The shared obligation's bound, from four charges at their expected counts.** -/
theorem prob_sharedBad_le_expected (q : Nat) (adversary : Adversary)
    (countCanonical countOffCanonical countOrdering : RecordedPair → Nat)
    (hshare : ∀ pair ∈ support (recordedPairedRun adversary),
      countCanonical pair + countOffCanonical pair + countOrdering pair +
        2 * AdversaryQueries.servedCount pair.2.1.1.1.signed ≤ q - 2 ^ subtreeHeight)
    (ordering : RecordedPair → Prop)
    (hinput : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
        InputBad (recordedTraceOf pair) ∧ ¬ ordering pair | recordedPairedRun adversary] ≤
      (expected (recordedPairedRun adversary) countCanonical + ((259 : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering pair |
        recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary) countOrdering / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
        RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 | recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary) countOffCanonical / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ SignerEvent pair |
        recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary)
          (fun pair => 2 * AdversaryQueries.servedCount pair.2.1.1.1.signed) /
        ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (prob_sharedBad_le_sum adversary ordering) ?_
  refine le_trans (add_le_add (add_le_add hinput hordering) (add_le_add hrecord hsigner)) ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  have hcounts : expected (recordedPairedRun adversary) countCanonical +
      expected (recordedPairedRun adversary) countOrdering +
        expected (recordedPairedRun adversary) countOffCanonical +
          expected (recordedPairedRun adversary)
            (fun pair => 2 * AdversaryQueries.servedCount pair.2.1.1.1.signed) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    rw [← expected_add, ← expected_add, ← expected_add]
    refine expected_le_of_le (recordedPairedRun adversary) _ _ fun pair hpair => ?_
    have := hshare pair hpair
    omega
  calc expected (recordedPairedRun adversary) countCanonical + ((259 : Nat) : ℝ≥0∞) +
        expected (recordedPairedRun adversary) countOrdering +
          (expected (recordedPairedRun adversary) countOffCanonical +
            expected (recordedPairedRun adversary)
              (fun pair => 2 * AdversaryQueries.servedCount pair.2.1.1.1.signed))
      = expected (recordedPairedRun adversary) countCanonical +
          expected (recordedPairedRun adversary) countOrdering +
            expected (recordedPairedRun adversary) countOffCanonical +
              expected (recordedPairedRun adversary)
                (fun pair => 2 * AdversaryQueries.servedCount pair.2.1.1.1.signed) +
                  ((259 : Nat) : ℝ≥0∞) := add_rearrange _ _ _ _ _
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add hcounts le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The join, at constants

The same thing with the four counts constant. It is kept because a cap-shaped charge produces
exactly this, and it is sound — but its four constants must be bounds on the *expected* counts,
not on the counts themselves, for the reason in the header. -/

/-- **The shared obligation's bound, from four charges at constant counts.** -/
theorem prob_sharedBad_le (q : Nat) (adversary : Adversary) (qc qp qm qs : Nat)
    (hsum : qc + qp + qm + qs ≤ q - 2 ^ subtreeHeight)
    (ordering : RecordedPair → Prop)
    (hinput : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
        InputBad (recordedTraceOf pair) ∧ ¬ ordering pair | recordedPairedRun adversary] ≤
      ((qc + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering pair |
        recordedPairedRun adversary] ≤ ((qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
        RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 | recordedPairedRun adversary] ≤
      ((qp : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ SignerEvent pair |
        recordedPairedRun adversary] ≤ ((qs : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (prob_sharedBad_le_sum adversary ordering) ?_
  refine le_trans (add_le_add (add_le_add hinput hordering) (add_le_add hrecord hsigner)) ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

/-! ## The obligation

What each owner has to deliver, with the randomiser defect's reduction already proved and the
signer's condition already fixed. Only the four bounds and the budget's pathwise inequality are
left. -/

/-- **The shared obligation, from four charges at their expected counts.** -/
theorem sharedCharged_of_expected
    (ordering : (q : Nat) → Adversary → RecordedPair → Prop)
    (countCanonical countOffCanonical countOrdering :
      (q : Nat) → Adversary → RecordedPair → Nat)
    (hshare : ∀ q adversary, HasTotalBudget adversary q →
      ∀ pair ∈ support (recordedPairedRun adversary),
        countCanonical q adversary pair + countOffCanonical q adversary pair +
            countOrdering q adversary pair +
              2 * AdversaryQueries.servedCount pair.2.1.1.1.signed ≤ q - 2 ^ subtreeHeight)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
          ¬ ordering q adversary pair | recordedPairedRun adversary] ≤
        (expected (recordedPairedRun adversary) (countCanonical q adversary) +
          ((259 : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering q adversary pair |
          recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary) (countOrdering q adversary) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
          RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 | recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary) (countOffCanonical q adversary) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ SignerEvent pair |
          recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary)
            (fun pair => 2 * AdversaryQueries.servedCount pair.2.1.1.1.signed) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedCharged := by
  intro q adversary _ hbudget
  exact prob_sharedBad_le_expected q adversary (countCanonical q adversary)
    (countOffCanonical q adversary) (countOrdering q adversary) (hshare q adversary hbudget)
    (ordering q adversary) (hinput q adversary hbudget) (hordering q adversary hbudget)
    (hrecord q adversary hbudget) (hsigner q adversary hbudget)

/-- **The shared obligation, from four charges at constant counts.** Sound, and usable only when
each constant bounds its charge's *expected* count. -/
theorem sharedCharged_of_parts (qc qp qm qs : Nat)
    (ordering : (q : Nat) → Adversary → RecordedPair → Prop)
    (hsum : ∀ q : Nat, 1 ≤ q → qc + qp + qm + qs ≤ q - 2 ^ subtreeHeight)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
          ¬ ordering q adversary pair | recordedPairedRun adversary] ≤
        ((qc + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering q adversary pair |
          recordedPairedRun adversary] ≤ ((qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
          RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 | recordedPairedRun adversary] ≤
        ((qp : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ SignerEvent pair |
          recordedPairedRun adversary] ≤ ((qs : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedCharged := by
  intro q adversary hq hbudget
  exact prob_sharedBad_le q adversary qc qp qm qs (hsum q hq) (ordering q adversary)
    (hinput q adversary hbudget) (hordering q adversary hbudget) (hrecord q adversary hbudget)
    (hsigner q adversary hbudget)

/-! ## The signer's coincidence, in expectation form

`ClassGrowth.run_splitCost_eq_map` identifies the split-counted run with the plain one, so the
charge may be read at the instrumented presentation and the bound carried back. Done that way
the signer's coincidence comes out in expectation form with no new machinery, which is what the
answer side's coverage term did.

**It lands at the wrong count, and the reason is a fact about what the counter can see.**
`ClassGrowth.splitCost` is indexed by the **input**: one unit of the inside slot for a hash call
at an in-class input, whoever makes it. The adversary's in-class call and the signer's are calls
at the *same* input — that is the search attack restated — so no input-indexed cost can charge
one and not the other, and what comes out is the expectation of **every** in-class hash call.

A counter wrapped around the signer's own sub-computation does not repair it either, and the
same attack says why: with `SK.prf` hardcoded the adversary queries `N` framings of its own,
keeps the one whose answer hits, and makes **one** request. The signer then makes two in-class
calls and `served` is one, while the event fires at about `N / 2 ^ 128`. So no bound shaped
`Pr[event] ≤ f(the signer's own in-class calls)` holds for any `f`.

What makes `2 · served` correct is the **branch**, not a counter: on runs where the record does
not meet the class, the in-class entries are the signer's own and
`RandomiserProvenance.growthAtMostOn_prfClass_of_clean` gives `2 · served` with no instrumentation
at all. `SignerEvent` is that conditioned event, and the charge for it is what the join still
waits on. Neither generic charge reaches it: `ClassExpectation.prob_bad_le_expected_cost` and
`PotentialCharge.prob_fired_le` both run at the shared oracle, and the condition is about *who*
made a call, which that oracle cannot see — correctly, since the two callers' in-class calls are
calls at the same input. -/

open scoped Classical in
/-- **The signer's coincidence, charged at the expected number of in-class hash calls.** -/
theorem prob_signerHitsSeed_tail_le_expected (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : GoodWalk walk) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        SignerHitsSeed walk.1.1.2.1 walk.1.1.2.2 result.2 result.1.1.signed |
      tail adversary walk] ≤
      expected ((simulateQ KeygenUniform.rom
          (countQueries (ClassGrowth.splitCost (RandomizerGate.PrfClass walk.1.1.2.1)
            .hash .verification) (afterSeeds adversary walk.1.1))).run walk.2)
        (fun result => result.1.2 .hash) * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
  rw [tail, ClassGrowth.probEvent_splitCost (RandomizerGate.PrfClass walk.1.1.2.1)
    (inside := QueryKind.hash) (outside := QueryKind.verification) (by decide)
    (afterSeeds adversary walk.1.1) walk.2]
  refine le_trans (probEvent_mono fun result _ hhit =>
    bad_of_signerHitsSeed _ _ _ _ result.1 hhit) ?_
  exact ClassExpectation.prob_bad_le_expected_cost _ _ _ _ .hash
    (fun input hmember => le_of_eq
      (ClassGrowth.splitCost_inside _ _ _ input hmember).symm)
    (RandomizerGate.prob_randomizerHitsSeed_le walk.1.1.2.1)
    (fun _ _ hbad => hbad.1) (afterSeeds adversary walk.1.1) walk.2
    (RandomizerGate.cleanBad_of_canonical walk.1.1.2.2 walk.1.1.2.1 walk.1.2 walk.2 hgood.1
      (WarmedCharges.walk_cache_canonical hwalk))

end SlhDsaSecurity.SharedJoin

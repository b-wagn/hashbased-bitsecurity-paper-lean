import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserProvenance
import SlhDsaSecurity.Proof.ClassExpectation

/-!
# The shared side's four charges, added

`Obligations.SharedCharged` is one bound on `InputBad ∨ RandomiserBad`, and four charges pay for
it. This file is the join: the four taken in the shape their owners are producing, added under
the partition, and discharged against `(q - 2 ^ subtreeHeight + 259) / 2 ^ 128`.

It is written before three of the four have landed, and deliberately. The join is where a
mismatch between two charges surfaces last and costs most, so the shapes are fixed here first
and each owner can check its statement against the hypothesis it is expected to fill.

**What the four are.** The record's entries are classified by their first block — `PK.seed`
(canonical), `SK.prf` (`PRF_msg`), or message-class — and made exclusive by priority those three
are disjoint, so their counts add to the record's size, which is `Outcome.counts.work`. The
fourth charge is not about the record at all:

* the input half pays its canonical part, plus the forgery's own 259 claims;
* the ordering defect pays the message-class part, and is taken here as an arbitrary event the
  input half may exclude, because where it sits inside that half is the input half's business
  and not the sum's;
* the randomiser defect pays the `PRF_msg` part;
* the signer's coincidence pays twice the served requests.

**The counts have to be expectations, and that is the one thing the join forces.** Each charge
would naturally be stated at a *cap* — a constant `L` with the count at most `L` on every
supported run, as `ClassCharge.prob_badWithinClasses_le` and
`RandomiserProvenance.prob_signerHitsSeed_within_le` give it. Four such caps cannot be added.
The partition `work + 2 · served + 2 ^ subtreeHeight ≤ q` holds **per run**, and the split
between `work` and `served` is a property of the run: one adversary may spend the budget
entirely on its own queries and another entirely on requests, so an almost-sure cap for each
count has to cover its own worst run, and four worst-case caps overshoot by a factor the
obligation has no room for.

Expectations add where caps do not, because they add *pathwise*:
`ClassExpectation.expected_add` and `expected_le_of_le` turn `∀ run, Σ counts ≤ q - 2 ^ subtreeHeight`
into `Σ expectations ≤ q - 2 ^ subtreeHeight` directly. That is the same move the answer side
already made for its coverage term (`TapeFactor.prob_exists_hit_le_expected`, "the statement the
two-class bound needs and the one a fixed-limit charge cannot be averaged into"), and
`ClassExpectation.add_le_of_shared_budget` is its two-term form. So `prob_sharedBad_le_expected`
is the join, and `prob_sharedBad_le` — the same thing at four constants — is kept only because
it is what a cap-shaped charge produces, with the warning that its four constants must be
expectation-level bounds and not almost-sure ones.

**Why the randomiser side is taken as a reduction rather than as a bound.** Its own statement,
`RandomiserProvenance.randomiserBad_source`, hands the record back *existentially over the
support*, and as a predicate on the run that is near-vacuous — `∃ record, card ≤ work + 1 ∧
∃ input ∈ record, …` is satisfied by a one-element multiset. So the record's event has to become
a predicate on a run that carries the record as a value, which is `RecordedTail`'s business, and
what the sum needs from it is exactly the dichotomy with that predicate in place of the
existential. `hrandomiser` is that, and nothing more.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharedJoin

open Security WarmedGame RoutedSplit ReplayGate Target RandomiserProvenance ClassExpectation

/-- What the shared side's events are stated on: a walk and the game that followed it. -/
abbrev Pair : Type :=
  (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
    ((Outcome × Nat) × QueryCache HashSpec)

/-- The trace the shared side's events read, assembled from a paired run's value. -/
abbrev traceOf (pair : Pair) : RoutedSplit.Trace := ((pair.1.1, pair.2.1), pair.2.2)

/-! ## The union bound

The shared event is covered by the four, and this is the only step that knows which event is
which. Everything after it is arithmetic on the counts. -/

/-- **The shared event is covered by the four.** The input half may exclude the ordering defect,
and the randomiser defect splits into its record's event and the signer's coincidence. -/
theorem prob_sharedBad_le_sum (adversary : Adversary)
    (ordering recordPrf signer : Pair → Prop)
    (hrandomiser : ∀ pair ∈ support (pairedRun adversary), GoodWalk pair.1 →
      RandomiserBad (traceOf pair) → recordPrf pair ∨ signer pair) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      Pr[fun pair : Pair => GoodWalk pair.1 ∧ InputBad (traceOf pair) ∧ ¬ ordering pair |
          pairedRun adversary] +
        Pr[fun pair : Pair => GoodWalk pair.1 ∧ ordering pair | pairedRun adversary] +
        (Pr[fun pair : Pair => GoodWalk pair.1 ∧ recordPrf pair | pairedRun adversary] +
          Pr[fun pair : Pair => GoodWalk pair.1 ∧ signer pair | pairedRun adversary]) := by
  classical
  refine le_trans (probEvent_mono (q := fun pair : Pair =>
    ((GoodWalk pair.1 ∧ InputBad (traceOf pair) ∧ ¬ ordering pair) ∨
        (GoodWalk pair.1 ∧ ordering pair)) ∨
      ((GoodWalk pair.1 ∧ recordPrf pair) ∨ (GoodWalk pair.1 ∧ signer pair))) ?_) ?_
  · rintro pair hpair ⟨hgood, hinputBad | hrandomiserBad⟩
    · by_cases hord : ordering pair
      · exact Or.inl (Or.inr ⟨hgood, hord⟩)
      · exact Or.inl (Or.inl ⟨hgood, hinputBad, hord⟩)
    · exact Or.inr ((hrandomiser pair hpair hgood hrandomiserBad).imp
        (fun hrec => ⟨hgood, hrec⟩) fun hsigner => ⟨hgood, hsigner⟩)
  · refine le_trans (probEvent_or_le _ _ _) (add_le_add ?_ ?_)
    · exact probEvent_or_le _ _ _
    · exact probEvent_or_le _ _ _

/-! ## The join, at expectations

The four counts are read off the paired run, and the only thing asked of them is that they
partition the budget **on every supported run**. `ClassExpectation.expected_add` then makes the
four expectations add to the expectation of the sum, and `expected_le_of_le` bounds that by the
budget. No charge is bounded on its own. -/

/-- The rearrangement the four-term sum needs, at abstract summands so that it stays cheap. -/
theorem add_rearrange (a m p s c : ℝ≥0∞) : a + c + m + (p + s) = a + m + p + s + c := by
  ring

set_option maxRecDepth 4000 in
/-- **The shared obligation's bound, from four charges at their expected counts.** -/
theorem prob_sharedBad_le_expected (q : Nat) (adversary : Adversary)
    (countCanonical countPrf countMessage countServed : Pair → Nat)
    (hshare : ∀ pair ∈ support (pairedRun adversary),
      countCanonical pair + countPrf pair + countMessage pair + countServed pair ≤
        q - 2 ^ subtreeHeight)
    (ordering recordPrf signer : Pair → Prop)
    (hinput : Pr[fun pair : Pair => GoodWalk pair.1 ∧ InputBad (traceOf pair) ∧
        ¬ ordering pair | pairedRun adversary] ≤
      (expected (pairedRun adversary) countCanonical + ((259 : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : Pr[fun pair : Pair => GoodWalk pair.1 ∧ ordering pair | pairedRun adversary] ≤
      expected (pairedRun adversary) countMessage / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : Pr[fun pair : Pair => GoodWalk pair.1 ∧ recordPrf pair | pairedRun adversary] ≤
      expected (pairedRun adversary) countPrf / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : Pr[fun pair : Pair => GoodWalk pair.1 ∧ signer pair | pairedRun adversary] ≤
      expected (pairedRun adversary) countServed / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrandomiser : ∀ pair ∈ support (pairedRun adversary), GoodWalk pair.1 →
      RandomiserBad (traceOf pair) → recordPrf pair ∨ signer pair) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (prob_sharedBad_le_sum adversary ordering recordPrf signer hrandomiser) ?_
  refine le_trans (add_le_add (add_le_add hinput hordering) (add_le_add hrecord hsigner)) ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  have hcounts : expected (pairedRun adversary) countCanonical +
      expected (pairedRun adversary) countMessage +
        expected (pairedRun adversary) countPrf +
          expected (pairedRun adversary) countServed ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    rw [← expected_add, ← expected_add, ← expected_add]
    refine expected_le_of_le (pairedRun adversary) _ _ fun pair hpair => ?_
    have := hshare pair hpair
    omega
  calc expected (pairedRun adversary) countCanonical + ((259 : Nat) : ℝ≥0∞) +
        expected (pairedRun adversary) countMessage +
          (expected (pairedRun adversary) countPrf + expected (pairedRun adversary) countServed)
      = expected (pairedRun adversary) countCanonical +
          expected (pairedRun adversary) countMessage +
            expected (pairedRun adversary) countPrf +
              expected (pairedRun adversary) countServed + ((259 : Nat) : ℝ≥0∞) :=
        add_rearrange _ _ _ _ _
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add hcounts le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The join, at constants

The same thing with the four counts constant. It is kept because a cap-shaped charge produces
exactly this, and it is sound — but its four constants must be bounds on the *expected* counts,
not on the counts themselves. A charge that only bounds its count almost surely cannot fill
these hypotheses at constants whose sum fits, for the reason in the header: the split between
`work` and `served` is a property of the run. -/

/-- **The shared obligation's bound, from four charges at constant counts.** -/
theorem prob_sharedBad_le (q : Nat) (adversary : Adversary) (qc qp qm qs : Nat)
    (hsum : qc + qp + qm + qs ≤ q - 2 ^ subtreeHeight)
    (ordering recordPrf signer : Pair → Prop)
    (hinput : Pr[fun pair : Pair => GoodWalk pair.1 ∧ InputBad (traceOf pair) ∧
        ¬ ordering pair | pairedRun adversary] ≤
      ((qc + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : Pr[fun pair : Pair => GoodWalk pair.1 ∧ ordering pair | pairedRun adversary] ≤
      ((qm : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : Pr[fun pair : Pair => GoodWalk pair.1 ∧ recordPrf pair | pairedRun adversary] ≤
      ((qp : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsigner : Pr[fun pair : Pair => GoodWalk pair.1 ∧ signer pair | pairedRun adversary] ≤
      ((qs : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrandomiser : ∀ pair ∈ support (pairedRun adversary), GoodWalk pair.1 →
      RandomiserBad (traceOf pair) → recordPrf pair ∨ signer pair) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧
        (InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair)) | pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (prob_sharedBad_le_sum adversary ordering recordPrf signer hrandomiser) ?_
  refine le_trans (add_le_add (add_le_add hinput hordering) (add_le_add hrecord hsigner)) ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

/-! ## The signer's coincidence, filled in

The fourth charge is proved, so it is not left as a hypothesis for long: at the cap form it is
`RandomiserProvenance.prob_signerHitsSeed_paired_within_le`, and its event is the one
`randomiserBad_source` hands back, with the growth conjunct the sharp count comes from. -/

/-- The signer's half of the randomiser defect, as the join reads it. -/
def SignerEvent (limit : Nat) (pair : Pair) : Prop :=
  SignerHitsSeed pair.1.1.1.2.1 pair.1.1.1.2.2 pair.2.2 pair.2.1.1.signed ∧
    ClassCharge.GrowthAtMostOn (RandomizerGate.PrfClass pair.1.1.1.2.1) pair.1.2 pair.2.2 limit

/-- **The fourth hypothesis, discharged.** -/
theorem prob_signerEvent_le (adversary : Adversary) (q qs : Nat)
    (hbudget : HasTotalBudget adversary q) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧ SignerEvent qs pair | pairedRun adversary] ≤
      ((qs : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  prob_signerHitsSeed_paired_within_le adversary q qs hbudget

/-- **The shared obligation itself**, from the three charges that are still open, with the
signer's filled in.

**Sound, but not instantiable at a small `qs`, and the reason is the one in the header.** The
signer's charge holds at *every* constant `qs`, because the growth is a conjunct of its event
rather than a hypothesis — but `hrandomiser` then has to deliver that conjunct, and
`randomiserBad_source` gives it only as `2 · served`, which is a property of the run. The only
constant that bounds `2 · served` on every run is the whole budget. So this shape needs each
charge's constant to bound its *expected* count, and the honest version of the assembly is
`prob_sharedBad_le_expected` once all four charges are stated there;
`ClassExpectation.prob_bad_le_expected` is the generic tool for moving one of them, and what it
asks for is the tail in its `countQueries (classCost …)` presentation. -/
theorem sharedCharged_of_parts (qs : Nat)
    (ordering recordPrf : (q : Nat) → Adversary → Pair → Prop)
    (qcOf qpOf qmOf : (q : Nat) → Adversary → Nat)
    (hsum : ∀ q adversary, HasTotalBudget adversary q →
      qcOf q adversary + qpOf q adversary + qmOf q adversary + qs ≤ q - 2 ^ subtreeHeight)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : Pair => GoodWalk pair.1 ∧ InputBad (traceOf pair) ∧
          ¬ ordering q adversary pair | pairedRun adversary] ≤
        ((qcOf q adversary + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : Pair => GoodWalk pair.1 ∧ ordering q adversary pair |
          pairedRun adversary] ≤
        ((qmOf q adversary : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrecord : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : Pair => GoodWalk pair.1 ∧ recordPrf q adversary pair |
          pairedRun adversary] ≤
        ((qpOf q adversary : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hrandomiser : ∀ q adversary, HasTotalBudget adversary q →
      ∀ pair ∈ support (pairedRun adversary), GoodWalk pair.1 →
        RandomiserBad (traceOf pair) →
          recordPrf q adversary pair ∨ SignerEvent qs pair) :
    Obligations.SharedCharged := by
  intro q adversary _ hbudget
  exact prob_sharedBad_le q adversary (qcOf q adversary) (qpOf q adversary) (qmOf q adversary)
    qs (hsum q adversary hbudget) (ordering q adversary) (recordPrf q adversary)
    (SignerEvent qs) (hinput q adversary hbudget) (hordering q adversary hbudget)
    (hrecord q adversary hbudget) (prob_signerEvent_le adversary q qs hbudget)
    (hrandomiser q adversary hbudget)

end SlhDsaSecurity.SharedJoin

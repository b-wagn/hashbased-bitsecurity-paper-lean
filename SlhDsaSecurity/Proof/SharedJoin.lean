import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassExpectation
import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.AnswerSide
import SlhDsaSecurity.Proof.RecordedBudget

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

/-! ## The counts, read off the record

Each charge's count is a **part of the run's own record**, and the parts are named here so that
the owners prove containments into one observable rather than three different counts.

Why the record and not the cache's growth: a sensitive probe may be answered from the walk's
table and install nothing, so growth cannot report it; and the plain pair carries no split
counter, so a slot-based count has nowhere to live. The record has neither problem, and it is
the observable the accounting is already written in — `Multiset.card record = counts.work`
exactly, which is what ties every part of it to the budget.

**What each owner proves is a containment, not a conversion.** A charge keeps whatever probe
list its own handler produces and shows that list sits inside the record's part of its class;
`ProbesIn` is that obligation and `card_le_of_probesIn` is what it buys. Nothing has to be
restated at a counter.

The two parts are disjoint on a good walk — a canonical input opens with `PK.seed ‖ ADRS` and a
message input with a randomiser, and `HashSeparation` separates them once the key is no
coincidence — so their cardinalities add to at most the record's, which is the work, which with
key generation's reserved spend is `q - 2 ^ subtreeHeight`. That is `card_parts_le_budget`, and
with the forgery's `259` claims against the `512` key generation puts back it is the whole of
the shared side's arithmetic. -/

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.tail
  RecordedTail.recordedAfterSeeds RecordedTail.recordedTail

/-- The run's own record. -/
abbrev recordOf (pair : RecordedPair) : Multiset Bytes := pair.2.1.1.2

open scoped Classical in
/-- **The input half's count**: the record's entries that are canonical inputs of the walk's own
cells. -/
noncomputable def recordCanonical (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter (HonestProbes.Canonical pair.1.1.1.2.2 pair.1.1.2)

open scoped Classical in
/-- **The ordering defect's count**: the record's entries that are message inputs at the run's
own key and are not canonical.

The exclusion is in the definition rather than in a hypothesis, which is what makes the two
parts disjoint on *every* run and so keeps `GoodWalk` out of the arithmetic entirely. It costs
the owner nothing: on a good walk no canonical input is a message input
(`canonical_not_messageInput`), so `mem_recordMessageClass` lets a containment be proved against
the plain predicate. -/
noncomputable def recordMessageClass (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter fun input =>
    CombinedCharge.IsMessageInput (RoutedSplit.keyOf (recordedTraceOf pair)) input ∧
      ¬ HonestProbes.Canonical pair.1.1.1.2.2 pair.1.1.2 input

/-- **What a charge has to prove about its own probes**: that they sit inside one part of the
record. -/
def ProbesIn (part probes : RecordedPair → Multiset Bytes) (adversary : Adversary) : Prop :=
  ∀ pair ∈ support (recordedPairedRun adversary), probes pair ≤ part pair

theorem card_le_of_probesIn {part probes : RecordedPair → Multiset Bytes}
    {adversary : Adversary} (hprobes : ProbesIn part probes adversary) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) :
    Multiset.card (probes pair) ≤ Multiset.card (part pair) :=
  Multiset.card_le_card (hprobes pair hpair)

/-! ## From a part of the record to the budget -/

/-- A supported pair is a supported walk followed by a supported recorded tail. -/
theorem mem_support_recordedPairedRun {adversary : Adversary} {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) :
    pair.1 ∈ support graphWalk ∧
      pair.2 ∈ support (RecordedTail.recordedTail adversary pair.1) := by
  obtain ⟨walk, hwalk, result, hresult, hvalue⟩ : ∃ walk ∈ support graphWalk,
      ∃ result ∈ support (RecordedTail.recordedTail adversary walk), (walk, result) = pair := by
    simpa [recordedPairedRun, eq_comm] using hpair
  subst hvalue
  exact ⟨hwalk, hresult⟩

/-- **The record is exactly the work the run charges**, read at the recorded tail. -/
theorem card_record_eq_work (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk)) :
    Multiset.card result.1.1.2 = result.1.1.1.counts.work := by
  rw [RecordedTail.recordedTail] at hresult
  exact RecordedTail.card_eq_work adversary walk.1.1 walk.2 (result.1.1, result.2)
    (WarmedSplit.mem_support_of_countAllHashes _ walk.2 result hresult)

set_option maxHeartbeats 1000000 in
/-- **A canonical input of the walk's cells is not a message input at the run's key**, the key
being no coincidence on a good walk. -/
theorem canonical_not_messageInput (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : GoodWalk walk)
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk))
    (input : Bytes) (hcanonical : HonestProbes.Canonical walk.1.1.2.2 walk.1.2 input) :
    ¬ CombinedCharge.IsMessageInput
      (RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2)) input := by
  obtain ⟨parent, rfl⟩ := hcanonical
  have hkey : RoutedSplit.keyOf ((walk.1, (result.1.1.1, result.1.2)), result.2) =
      SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2 := by
    rw [RoutedSplit.keyOf]
    exact AnswerSide.generatedKey_eq_walk adversary hwalk
      (result := ((result.1.1.1, result.1.2), result.2))
      (RecordedTail.mem_support_tail_of_recorded adversary hresult)
  rw [hkey]
  exact WarmedCharges.not_messageInput_canonical walk.1.1.2.2 walk.1.2 _
    (AnswerSide.not_possible_generatedKey hwalk hgood.2) withinBounds_structural parent

open scoped Classical in
/-- **A message input of the record is in the ordering defect's part**, on a good walk, where
nothing canonical is one. So the owner proves its containment against the plain predicate. -/
theorem mem_recordMessageClass (adversary : Adversary) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) (hgood : GoodWalk pair.1)
    {input : Bytes} (hmem : input ∈ recordOf pair)
    (hmessage : CombinedCharge.IsMessageInput (RoutedSplit.keyOf (recordedTraceOf pair)) input) :
    input ∈ recordMessageClass pair := by
  classical
  obtain ⟨hwalk, hresult⟩ := mem_support_recordedPairedRun hpair
  rw [recordMessageClass, Multiset.mem_filter]
  exact ⟨hmem, hmessage, fun hcanonical =>
    canonical_not_messageInput adversary hwalk hgood hresult input hcanonical hmessage⟩

open scoped Classical in
/-- **The two parts fit inside the record**, being disjoint by construction and so on every
run. -/
theorem card_parts_le_record (pair : RecordedPair) :
    Multiset.card (recordCanonical pair) + Multiset.card (recordMessageClass pair) ≤
      Multiset.card (recordOf pair) := by
  classical
  have hdisjoint : ∀ input ∈ recordOf pair,
      ¬ (HonestProbes.Canonical pair.1.1.1.2.2 pair.1.1.2 input ∧
        (CombinedCharge.IsMessageInput (RoutedSplit.keyOf (recordedTraceOf pair)) input ∧
          ¬ HonestProbes.Canonical pair.1.1.1.2.2 pair.1.1.2 input)) := by
    rintro input - ⟨hcanonical, -, hnot⟩
    exact hnot hcanonical
  rw [recordCanonical, recordMessageClass, ← Multiset.card_add, Multiset.filter_add_filter,
    Multiset.filter_eq_nil.mpr hdisjoint, add_zero]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- **The two parts fit inside the budget**, with key generation's spend reserved for the
forgery's claims. -/
theorem card_parts_le_budget (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) :
    Multiset.card (recordCanonical pair) + Multiset.card (recordMessageClass pair) ≤
      q - 2 ^ subtreeHeight := by
  obtain ⟨hwalk, hresult⟩ := mem_support_recordedPairedRun hpair
  have hparts : Multiset.card (recordCanonical pair) +
      Multiset.card (recordMessageClass pair) ≤ Multiset.card (recordOf pair) :=
    card_parts_le_record pair
  have hwork : Multiset.card (recordOf pair) = pair.2.1.1.1.counts.work :=
    card_record_eq_work adversary hresult
  have hbound : pair.2.1.1.1.counts.work + 2 ^ subtreeHeight ≤ q :=
    RecordedBudget.work_add_pow_le_of_budget_tail hbudget hwalk
      (RecordedTail.mem_support_tail_of_recorded adversary hresult)
  omega

/-! ## The join, at the three terms the repair leaves

The input half at the record's canonical part, the forgery's `259` claims, and the ordering
defect at the record's message-class part. The randomiser defect's term and the signer's
coincidence are gone with the proxy they paid for.

The shared event is taken **abstractly**. Which disjuncts the split names is the split's
business and is still moving — the third stops being `ReplayGate.RandomiserBad` and becomes a
late-disclosure event, which may arrive as a hypothesis on the answer side rather than as a
disjunct — and the sum does not care: all it needs is that the event is covered by the input
half's and the ordering defect's, which is `hcover`.

`hshare` is gone too. The two counts are parts of one record and disjoint by construction, so
`card_parts_le_budget` proves what used to be assumed. That is the whole of the shared side's
arithmetic, and it closes on the nose: `card canonical + card message-class ≤ work`, and
`work + 2 ^ subtreeHeight ≤ q`, so the three terms are `(q - 2 ^ subtreeHeight) + 259`. -/

set_option maxRecDepth 4000 in
/-- **The shared obligation's bound, at three terms read off the record.** -/
theorem prob_sharedBad_le_three (q : Nat) (adversary : Adversary)
    (hbudget : HasTotalBudget adversary q)
    (shared : Pair → Prop) (inputBad ordering : RecordedPair → Prop)
    (hcover : ∀ pair ∈ support (recordedPairedRun adversary), GoodWalk pair.1 →
      shared (forgetRecord pair) → (inputBad pair ∧ ¬ ordering pair) ∨ ordering pair)
    (hinput : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ inputBad pair ∧ ¬ ordering pair |
        recordedPairedRun adversary] ≤
      (expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordCanonical pair)) + ((259 : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering pair |
        recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordMessageClass pair)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : Pair => GoodWalk pair.1 ∧ shared pair | pairedRun adversary] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_pairedRun_eq]
  refine le_trans (probEvent_mono (q := fun pair : RecordedPair =>
    (GoodWalk pair.1 ∧ inputBad pair ∧ ¬ ordering pair) ∨
      (GoodWalk pair.1 ∧ ordering pair)) ?_) ?_
  · rintro pair hpair ⟨hgood, hshared⟩
    exact (hcover pair hpair hgood hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord =>
      ⟨hgood, hord⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add hinput hordering) ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  have hcounts : expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordCanonical pair)) +
      expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordMessageClass pair)) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    rw [← expected_add]
    exact expected_le_of_le (recordedPairedRun adversary) _ _ fun pair hpair =>
      card_parts_le_budget adversary q hbudget hpair
  calc expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordCanonical pair)) + ((259 : Nat) : ℝ≥0∞) +
        expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordMessageClass pair))
      = expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordCanonical pair)) +
          expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordMessageClass pair)) +
              ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add hcounts le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-- **The shared obligation, from the two charges the repair leaves.** Stated at the split's
current disjuncts; when the third stops being `RandomiserBad` only `hcover` changes, since
`prob_sharedBad_le_three` takes the shared event abstractly. -/
theorem sharedCharged_of_three
    (inputBad ordering : (q : Nat) → Adversary → RecordedPair → Prop)
    (hcover : ∀ q adversary, HasTotalBudget adversary q →
      ∀ pair ∈ support (recordedPairedRun adversary), GoodWalk pair.1 →
        (InputBad (recordedTraceOf pair) ∨ RandomiserBad (recordedTraceOf pair)) →
          (inputBad q adversary pair ∧ ¬ ordering q adversary pair) ∨
            ordering q adversary pair)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ inputBad q adversary pair ∧
          ¬ ordering q adversary pair | recordedPairedRun adversary] ≤
        (expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordCanonical pair)) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering q adversary pair |
          recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordMessageClass pair)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedCharged := by
  intro q adversary _ hbudget
  exact prob_sharedBad_le_three q adversary hbudget
    (fun pair => InputBad (traceOf pair) ∨ RandomiserBad (traceOf pair))
    (inputBad q adversary) (ordering q adversary) (hcover q adversary hbudget)
    (hinput q adversary hbudget) (hordering q adversary hbudget)

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

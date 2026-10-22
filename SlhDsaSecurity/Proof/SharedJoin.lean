import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassExpectation
import SlhDsaSecurity.Proof.ClassGrowth
import SlhDsaSecurity.Proof.AnswerSide
import SlhDsaSecurity.Proof.RedrawCell
import SlhDsaSecurity.Proof.RecordedBudget
import SlhDsaSecurity.Proof.PairedAverage

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

/-- **A probe whose address locates a cell.** The input half's part is read at this and not at
canonicality, and the difference is a soundness point rather than a fit.

A probe is *canonical* at the walk's own cells exactly when its payload is the true cell — that
is, exactly when the guess is **right**. The per-cell charge gives every probe naming a
sensitive node's address one chance at a freshly drawn cell, so the weight has to count probes
with the right address and *any* payload. Narrowing the part to canonical probes would narrow
the charge to the hits, and the wrong guesses are precisely what the `2 ^ -128` pays for. It is
the narrowing that looks safe that makes the charge unsound. -/
def AimsSomewhere (publicSeed : Digest) (input : Bytes) : Prop :=
  GraphStakes.locate publicSeed input ≠ none

open scoped Classical in
/-- **The input half's count**: the record's entries whose address locates a cell. -/
noncomputable def recordAiming (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter (AimsSomewhere pair.1.1.1.2.2)

open scoped Classical in
/-- **The ordering defect's count**: the record's entries that are message inputs at the key the
**walk** generates and aim nowhere.

**The key is the walk's, and everything here names that one.** The walk's key is fixed before
the run, so a statement about it composes; the run's key is a function of the result, and naming
it would drag `AnswerSide.generatedKey_eq_walk` into every use and let the same defect be stated
twice at two keys that are equal only on the support. That lemma is applied once, inside
`not_aimsSomewhere_messageInput`, where the support is in hand, and no producer ever writes the
run's key.

The aiming exclusion is in the definition rather than in a hypothesis, which is what makes the
two parts disjoint on *every* run and so keeps `GoodWalk` out of the arithmetic entirely. It
costs the owner nothing: on a good walk a message input aims nowhere
(`not_aimsSomewhere_messageInput`), so `mem_recordMessageClass` lets a containment be proved
against the plain predicate. -/
noncomputable def recordMessageClass (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter fun input =>
    CombinedCharge.IsMessageInput
        (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2) input ∧
      ¬ AimsSomewhere pair.1.1.1.2.2 input

/-- **What a charge has to prove about its own probes**: that they sit inside one part of the
record.

**The spelling of `probes` matters, and it is the multiset of the list.** An owner whose
handler yields a list — `DigestTape.Record` and the input half's record both do — converts by
`↑(entries.map Prod.fst)`, whose `Multiset.card` is `entries.length`. A `toFinset` would also
satisfy the containment while silently *lowering* the count, and the charge is stated at the
count, so it would break the owner's own bound rather than this one — which is the worst place
for it to break, since the join would still typecheck. -/
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
/-- **A message input at the walk's key aims nowhere**, the key being no coincidence on a good
walk: an aiming address is a structural node's, so it sits inside `HashSeparation`'s bounds and
a message input cannot be one. Stated at the walk's key, it needs no run at all.

This replaces the canonicality separation, and it is the easier of the two: aiming is about the
address alone, and the address is where the separation already lives. -/
theorem not_aimsSomewhere_messageInput
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (hgood : GoodWalk walk)
    (input : Bytes) (hmessage : CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) input) :
    ¬ AimsSomewhere walk.1.1.2.2 input := by
  obtain ⟨randomizer, message, rfl⟩ := hmessage
  rw [AimsSomewhere, RedrawCell.locate_messageInput walk.1.1.2.2 randomizer _ message
    (AnswerSide.not_possible_generatedKey hwalk hgood.2)]
  exact fun hne => hne rfl

/-- **The run's key is the walk's**, on a supported pair. This is the one place
`AnswerSide.generatedKey_eq_walk` is applied, so that no statement downstream has to carry it. -/
theorem keyOf_eq_walkKey (adversary : Adversary) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) :
    RoutedSplit.keyOf (recordedTraceOf pair) =
      SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2 := by
  obtain ⟨hwalk, hresult⟩ := mem_support_recordedPairedRun hpair
  rw [RoutedSplit.keyOf]
  exact AnswerSide.generatedKey_eq_walk adversary hwalk
    (RecordedTail.mem_support_tail_of_recorded adversary hresult)

open scoped Classical in
/-- **A message input of the record is in the ordering defect's part**, on a good walk, where
nothing that aims is one. So the owner proves its containment against the plain predicate. -/
theorem mem_recordMessageClass (adversary : Adversary) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) (hgood : GoodWalk pair.1)
    {input : Bytes} (hmem : input ∈ recordOf pair)
    (hmessage : CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2) input) :
    input ∈ recordMessageClass pair := by
  classical
  obtain ⟨hwalk, -⟩ := mem_support_recordedPairedRun hpair
  rw [recordMessageClass, Multiset.mem_filter]
  exact ⟨hmem, hmessage, not_aimsSomewhere_messageInput hwalk hgood input hmessage⟩

open scoped Classical in
/-- **The two parts fit inside the record**, being disjoint by construction and so on every
run. -/
theorem card_parts_le_record (pair : RecordedPair) :
    Multiset.card (recordAiming pair) + Multiset.card (recordMessageClass pair) ≤
      Multiset.card (recordOf pair) := by
  classical
  have hdisjoint : ∀ input ∈ recordOf pair,
      ¬ (AimsSomewhere pair.1.1.1.2.2 input ∧
        (CombinedCharge.IsMessageInput
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            input ∧
          ¬ AimsSomewhere pair.1.1.1.2.2 input)) := by
    rintro input - ⟨haims, -, hnot⟩
    exact hnot haims
  rw [recordAiming, recordMessageClass, ← Multiset.card_add, Multiset.filter_add_filter,
    Multiset.filter_eq_nil.mpr hdisjoint, add_zero]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- **The two parts fit inside the budget**, with key generation's spend reserved for the
forgery's claims.

Read by the shared side at a pair that carries the recorder's recordings, through
`LateProbes.mem_support_forget`, because that pair's type and its projection to this one are
defined above this file. **A cleanup for after the obligation closes**: `LateProbes.SplitPair`
and `LateProbes.forgetRecordings` need only the two type abbreviations above and
`SplitPrefix.SplitState`, all of which are below this file, so moving them down would let this
be stated at the pair the shared side actually reads and the transport would go. Not worth
changing the join's surface for while two owners are still landing. -/
theorem card_parts_le_budget (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q) {pair : RecordedPair}
    (hpair : pair ∈ support (recordedPairedRun adversary)) :
    Multiset.card (recordAiming pair) + Multiset.card (recordMessageClass pair) ≤
      q - 2 ^ subtreeHeight := by
  obtain ⟨hwalk, hresult⟩ := mem_support_recordedPairedRun hpair
  have hparts : Multiset.card (recordAiming pair) +
      Multiset.card (recordMessageClass pair) ≤ Multiset.card (recordOf pair) :=
    card_parts_le_record pair
  have hwork : Multiset.card (recordOf pair) = pair.2.1.1.1.counts.work :=
    card_record_eq_work adversary hresult
  have hbound : pair.2.1.1.1.counts.work + 2 ^ subtreeHeight ≤ q :=
    RecordedBudget.work_add_pow_le_of_budget_tail hbudget hwalk
      (RecordedTail.mem_support_tail_of_recorded adversary hresult)
  omega

/-! ## The adapters, so the bridge is applied rather than merely present

`ProbesIn` and `card_le_of_probesIn` say what an owner has to prove and what it buys, but
getting from there to the hypotheses the join actually takes is four more lines, and two of the
three owners would each discover them. So the join does it.

The adapters also take the charge **per walk**, which is both the habit and the shape the
charges naturally prove: a charge is proved at a fixed walk, where the cells are fixed, and the
averaging is a separate step. Asking the owner for the paired form would be asking them to
perform that step; the adapter performs it instead.

A bridge that exists but sits unapplied is indistinguishable from a missing one at the moment
someone hands work over, and the cost lands on whoever assembles. -/

/-- **The paired run is the walk and then the recorded tail**, read at an event. -/
theorem probEvent_recordedPairedRun (adversary : Adversary) (event : RecordedPair → Prop) :
    Pr[event | recordedPairedRun adversary] =
      ∑' walk, Pr[= walk | graphWalk] *
        Pr[fun result => event (walk, result) |
          RecordedTail.recordedTail adversary walk] :=
  PairedAverage.probEvent_pairedWith (RecordedTail.recordedTail adversary) event

open scoped Classical in
/-- **The same, read at a count.** -/
theorem expected_recordedPairedRun (adversary : Adversary) (count : RecordedPair → Nat) :
    expected (recordedPairedRun adversary) count =
      ∑' walk, Pr[= walk | graphWalk] *
        expected (RecordedTail.recordedTail adversary walk)
          (fun result => count (walk, result)) :=
  PairedAverage.expected_pairedWith (RecordedTail.recordedTail adversary) count

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A charge proved walk by walk is a charge on the paired run.** The constant beside the
count survives the averaging because the walk's law has mass at most one. -/
theorem prob_le_expected_of_perWalk (adversary : Adversary) (event : RecordedPair → Prop)
    (count : RecordedPair → Nat) (extra : ℝ≥0∞)
    (hwalkwise : ∀ walk ∈ support graphWalk,
      Pr[fun result => event (walk, result) |
          RecordedTail.recordedTail adversary walk] ≤
        (expected (RecordedTail.recordedTail adversary walk)
          (fun result => count (walk, result)) + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | recordedPairedRun adversary] ≤
      (expected (recordedPairedRun adversary) count + extra) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  PairedAverage.prob_le_expected_of_perWalk (RecordedTail.recordedTail adversary) event count
    extra hwalkwise

/-! ## The two per-walk adapters, neither of which has a consumer

Both are sound and neither can serve the owner it was written for. `hinput_of_probesIn` takes
its charge per walk, which the input half cannot give, for the reason its own docstring sets
out. `hordering_of_probesIn` takes an `ordering` that is a predicate of the recorded pair, and
the ordering defect is not one — a recorded pair carries no recordings, and which side an entry
was filed on is the whole content of the defect. `SharedAssembly` closes the obligation without
either. They are kept until it closes, and the hazard a reader meeting them first should be
spared is reaching for one on the strength of its name. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The input half's hypothesis, from a containment and a walk-by-walk charge.**

**Sound, but the input half cannot use it, and nobody should reach for it on the strength of
its name.** The charge is taken *per walk*, and the input half's cannot be: conditioning on the
walk fixes the cell table, an adversary may be chosen knowing it, and at the walk whose cells it
hardcodes the input event has probability one against a bound near `2 ^ -100`. That is the
counterexample that moved `Obligations.SharedCharged` to the paired run in the first place; this
adapter inherits the per-walk shape and inherits the obstruction with it.

**The rule, which this is the third occasion for: a charge may be read at a fixed walk exactly
when the randomness it spends is drawn after the walk.** The ordering defect qualifies — what it
spends is the oracle's own fresh answers — and `hordering_of_probesIn` below is the adapter that
serves it. The input half spends a secret the walk already drew, and discharges
`prob_sharedBad_le_expected`'s `hinput` directly at `recordedPairedRun` instead. -/
theorem hinput_of_probesIn (adversary : Adversary) (inputBad ordering : RecordedPair → Prop)
    (probes : RecordedPair → Multiset Bytes)
    (hprobes : ProbesIn recordAiming probes adversary)
    (hcharge : ∀ walk ∈ support graphWalk,
      Pr[fun result => GoodWalk walk ∧ inputBad (walk, result) ∧ ¬ ordering (walk, result) |
          RecordedTail.recordedTail adversary walk] ≤
        (expected (RecordedTail.recordedTail adversary walk)
            (fun result => Multiset.card (probes (walk, result))) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ inputBad pair ∧ ¬ ordering pair |
        recordedPairedRun adversary] ≤
      (expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prob_le_expected_of_perWalk adversary _
    (fun pair => Multiset.card (probes pair)) _ hcharge) ?_
  exact ENNReal.div_le_div_right (add_le_add (expected_mono _ _ _
    fun pair hpair => card_le_of_probesIn hprobes hpair) le_rfl) _

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering defect's hypothesis, from a containment and a walk-by-walk charge.** This is
the adapter the per-walk shape is sound for: the randomness the defect spends is the oracle's
own fresh answers, drawn after the walk, so fixing the walk gives an adversary nothing. See
`hinput_of_probesIn` for the half this does *not* serve. -/
theorem hordering_of_probesIn (adversary : Adversary) (ordering : RecordedPair → Prop)
    (probes : RecordedPair → Multiset Bytes)
    (hprobes : ProbesIn recordMessageClass probes adversary)
    (hcharge : ∀ walk ∈ support graphWalk,
      Pr[fun result => GoodWalk walk ∧ ordering (walk, result) |
          RecordedTail.recordedTail adversary walk] ≤
        (expected (RecordedTail.recordedTail adversary walk)
            (fun result => Multiset.card (probes (walk, result))) + 0) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering pair |
        recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordMessageClass pair)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prob_le_expected_of_perWalk adversary
    (fun pair => GoodWalk pair.1 ∧ ordering pair)
    (fun pair => Multiset.card (probes pair)) 0 hcharge) ?_
  rw [add_zero]
  exact ENNReal.div_le_div_right (expected_mono _ _ _
    fun pair hpair => card_le_of_probesIn hprobes hpair) _

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
          (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
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
        (fun pair => Multiset.card (recordAiming pair)) +
      expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordMessageClass pair)) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    rw [← expected_add]
    exact expected_le_of_le (recordedPairedRun adversary) _ _ fun pair hpair =>
      card_parts_le_budget adversary q hbudget hpair
  calc expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞) +
        expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordMessageClass pair))
      = expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordAiming pair)) +
          expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordMessageClass pair)) +
              ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add hcounts le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-- **The shared obligation, from the two charges the repair leaves.** The split is two-way now,
so the shared event is `InputBad` alone; `prob_sharedBad_le_three` takes it abstractly, which is
why only `hcover` had to change when the randomiser defect went. -/
theorem sharedCharged_of_three
    (inputBad ordering : (q : Nat) → Adversary → RecordedPair → Prop)
    (hcover : ∀ q adversary, HasTotalBudget adversary q →
      ∀ pair ∈ support (recordedPairedRun adversary), GoodWalk pair.1 →
        InputBad (recordedTraceOf pair) →
          (inputBad q adversary pair ∧ ¬ ordering q adversary pair) ∨
            ordering q adversary pair)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ inputBad q adversary pair ∧
          ¬ ordering q adversary pair | recordedPairedRun adversary] ≤
        (expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
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
    (fun pair => InputBad (traceOf pair))
    (inputBad q adversary) (ordering q adversary) (hcover q adversary hbudget)
    (hinput q adversary hbudget) (hordering q adversary hbudget)

/-! ## The cover costs nothing

`hcover` reads like the step where the split is justified, and at the instantiation the shared
side actually uses it is **excluded middle** and nothing else. Taking `inputBad` to be the
shared event itself, the two parts are "the event with the defect ruled out" and "the defect",
and those cover the event for *any* `ordering` whatever.

Two things follow, and both are worth saying where the hypothesis used to sit.

* It is free, so `sharedCharged_of_two` below carries it internally instead of owing it. The
  shared side's two obligations are the two charges; there is no third.
* It does not look at `ordering`, so **the ordering thread may restate its event however it
  likes** — on the record alone, on the recordings, on the final cache — and this step does not
  move. The thread that found `hordering_of_probesIn` cannot accept an event defined by which
  side an entry was filed on, because a `RecordedPair` carries no recordings; whatever it
  settles on, the cover is the same two lines. The content of the split lives entirely in
  `hinput`, which is where `¬ ordering` is *assumed* and has to be converted into a charge
  against the aiming part. -/

/-- **The two-part cover of an event is excluded middle.** No property of `ordering` is used;
in particular it need not be an event of the run at all — and no property of the pair either,
which is why it is stated at any type. The second caller reads a pair that carries the
recorder's two recordings, since the ordering defect is not a predicate of the recorded pair,
and a lemma that looked at nothing should not have to be restated for it. -/
theorem cover_of_em {α : Type} (shared ordering : α → Prop) (pair : α)
    (hshared : shared pair) :
    (shared pair ∧ ¬ ordering pair) ∨ ordering pair := by
  classical
  by_cases hord : ordering pair
  · exact Or.inr hord
  · exact Or.inl ⟨hshared, hord⟩

/-- **The shared obligation, from the two charges and nothing else.** This is
`sharedCharged_of_three` at the instantiation the shared side uses — the input half's event is
the shared event — with `hcover` discharged by `cover_of_em`. The ordering defect's event stays
abstract. -/
theorem sharedCharged_of_two
    (ordering : (q : Nat) → Adversary → RecordedPair → Prop)
    (hinput : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
          ¬ ordering q adversary pair | recordedPairedRun adversary] ≤
        (expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hordering : ∀ q adversary, HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ ordering q adversary pair |
          recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordMessageClass pair)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedCharged :=
  sharedCharged_of_three (fun _ _ pair => InputBad (recordedTraceOf pair)) ordering
    (fun q adversary _ pair _ _ hshared =>
      cover_of_em (fun pair => InputBad (recordedTraceOf pair)) (ordering q adversary) pair
        hshared)
    hinput hordering

/-! ## The four-term union-bound route, superseded

Everything from here to the end of the file is the route built when the split still named a
randomiser defect and the signer's seed coincidence: four events, four counts, one budget.
The two-way split retired the first and the replay branch's closure retired the second, and
`SharedAssembly.sharedCharged_of_parts` now closes `Obligations.SharedCharged` from the input
half's bullet and the ordering term alone. Nothing outside this file reaches any of it.

It is retained until the obligation closes, not because anything here is wrong — it is not —
but because deleting a route while two owners are still landing is the trade that has cost
twice. `SignerEvent` goes with it when it goes.

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

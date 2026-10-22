import SlhDsaSecurity.Proof.SharedAssembly
import SlhDsaSecurity.Proof.ProbeContainment
import SlhDsaSecurity.Proof.RecordedChain
import SlhDsaSecurity.Proof.ServedBridge
import SlhDsaSecurity.Proof.ServingTable

/-!
# The input half's bullet, reduced to one inequality

`SharedAssembly.InputBullet` is what the join takes from this half: an event at the split pair,
bounded by **an expected count plus `259`**, over `2 ^ 128`. This file does the two steps between
that and the thing the half's chain produces, and both are free:

* **the ordering term is dropped**, because the bound below is proved for the strictly larger
  event without it — so the bullet holds for *any* `ordering`, of any type, and the defect's
  owner may restate it however they like without this half moving;
* **the pair is forgotten**, by `LateProbes.probEvent_forget` and `ClassExpectation.expected_forget`
  at `FusedCoverage.forgetsTo` — the transport the split pair was introduced for.

`ClaimsCharged` is what is left, and it keeps the expected count.

**It cannot be a constant, and the reason is worth keeping in front of whoever reads this
next.** `RoutedSplit.InputBad` is an existential over the forgery's `259` claimed candidates, so
it is tempting to read the half as owing `259 / 2 ^ 128` — one chance per claim. That counts the
forgery's outputs. What the event asks of a claim is that it be `SensitiveQuery.Sensitive`: the
canonical input of a node whose staked cell is unavailable, **taking the value the table gives
it**. So the forgery must contain a *correct* unrevealed cell, and the adversary's chances at
one are its queries, not its outputs.

The test oracle is the authentication path. A FORS signature publishes the level-0 sibling
`F(PK.seed ‖ ADRS ‖ sk)` of a secret `sk` it did not reveal and whose cell is unavailable. The
adversary queries `F(PK.seed ‖ ADRS ‖ x)` for candidate `x` and compares with the published
sibling: one query per candidate, and on a hit it places the recovered secret among its claims
and the event holds with certainty. A constant bound is false by a factor of `q`.

The expected count is exactly the right payment, and it was always budgeted: the aiming part of
the record is *precisely* the probes whose address locates a cell, which is to say precisely
these tests, and `SharedAssembly.expected_parts_le_budget` has always paid
`aiming + messageClass ≤ q - 2 ^ subtreeHeight`.

`bullet_of_bound` below is the constant-hypothesis implication. It is true, it is kept, and it
is the thing to point at if a constant is proposed here again — what is false is not the
implication but the belief that anything proves its hypothesis.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.InputBullet

open Security WarmedGame RoutedSplit Target ClassExpectation SharedJoin RandomiserRecord
  LateProbes SharedAssembly

/-- **The shape the half owes**: the claims charged at the recorded paired run, with no walk
fixed and no ordering term, and with the aiming part of the record paying for the tests the
adversary makes. This is the hypothesis the half's chain converges on. -/
def ClaimsCharged (adversary : Adversary) : Prop :=
  Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) |
      recordedPairedRun adversary] ≤
    (expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
      ((2 ^ 128 : Nat) : ℝ≥0∞)

/-- **The half's bullet, from the half's one remaining obligation.** The ordering predicate is
untouched — the bound is proved without its conjunct — so this holds at whatever shape that
defect is eventually stated in. -/
theorem bullet_of_claimsCharged (adversary : Adversary) (ordering : SplitPair → Prop)
    (hclaims : ClaimsCharged adversary) : SharedAssembly.InputBullet adversary ordering := by
  classical
  refine le_trans (probEvent_mono (q := fun pair : SplitPair =>
    GoodWalk (forgetRecordings pair).1 ∧ InputBad (recordedTraceOf (forgetRecordings pair)))
    (fun pair _ hpair => ⟨hpair.1, hpair.2.1⟩)) ?_
  rw [probEvent_forget (FusedCoverage.forgetsTo adversary)
      (fun pair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair)),
    expected_forget (FusedCoverage.forgetsTo adversary)
      (fun pair : RecordedPair => Multiset.card (recordAiming pair))]
  exact hclaims

/-- **The bullet from a constant, kept for what it rules out.** The implication is true and
costs nothing; what is false is that anything proves its hypothesis. A claim counts for the
event only when it carries the cell's *correct* value, and the signature's own authentication
path is a test for that — one query per candidate — so the chances are the adversary's queries
and a constant is short by a factor of `q`. `ClaimsCharged` is the statement to aim at. -/
theorem bullet_of_bound (adversary : Adversary) (ordering : SplitPair → Prop)
    (hbound : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) |
        recordedPairedRun adversary] ≤
      ((259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    SharedAssembly.InputBullet adversary ordering :=
  bullet_of_claimsCharged adversary ordering
    (le_trans hbound (ENNReal.div_le_div_right le_add_self _))


/-! ## The agreement this half consumes, named so it can be aimed at

The half's charge reads disclosure from the **carrier** — that is what the handler carries and
what `RedrawCell`'s availability is a predicate of — while `RoutedSplit.InputBad` reads it from
the **log**, through `ServedLog.disclosedByLog`. `ServedBridge` is where the two meet, and what
it asks for is `ServedAgree`: the carrier's served set and the log's are each contained in the
other, at which point `disclosedAt_subset_disclosedByLog` and its converse make the two
disclosure sets one `Finset` and the entries and the event are instantiated at the same object.

**This is stated as a hypothesis rather than proved here on purpose.** It is the only thing
between this half and its bullet that belongs to another owner, and the shape it arrives in has
to be the shape consumed: an unapplied bridge is indistinguishable from a missing one. So it is
written at the run this half's chain ends at — the handler's run of the linked game at a drawn
table, started from the empty carrier — with the key the walk's table determines, the log the
run's own value carries, and the cache the game's, which is the handler's read through
`RedrawCell.unionCache`. If what arrives differs, this is where it fails to elaborate. -/

open WalkTable TableTail in
/-- **The agreement, at the run the half's chain used to end at.**

**Superseded, and kept only so the name does not point nowhere.** `TableTail.handlerRun` is the
*stripped* game under `lazyProgram`, and it is the wrong run twice over: the stripped signer
cannot meet the charge's `htouched`, and `lazyProgram` files nothing, so its carrier has no
served set for `ServedAgree` to be about. `AgreesAtServingHandler` below is the shape to aim
at — the same agreement at `ServingTable.servingHandlerRun`. -/
def AgreesAtHandler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) : Prop :=
  ∀ (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (z : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × OpenCache.HandlerState),
    z ∈ support (handlerRun adversary prfSeed publicSeed table
      (HandlerCarrier.empty, record, count)) →
      ServedBridge.ServedAgree (keysOf prfSeed publicSeed table).2 z.2.1
        (((LinkedGame.outcomeOf z.1).1, (LinkedGame.outcomeOf z.1).1.counts.work),
          RedrawCell.unionCache publicSeed table z.2.1.cache)

open WalkTable TableTail in
/-- **The agreement, at the run this half ends at.** The honest game at a drawn table under the
handler that files, started from the empty carrier: the key the walk's table determines, the log
the run's own value carries, and the cache the game's, read through `RedrawCell.unionCache`.
If what arrives differs, this is where it fails to elaborate. -/
def AgreesAtServingHandler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) : Prop :=
  ∀ (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (z : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × OpenCache.HandlerState),
    z ∈ support (ServingTable.servingHandlerRun adversary prfSeed publicSeed table
      (HandlerCarrier.empty, record, count)) →
      ServedBridge.ServedAgree (keysOf prfSeed publicSeed table).2 z.2.1
        (((LinkedGame.outcomeOf z.1).1, (LinkedGame.outcomeOf z.1).1.counts.work),
          RedrawCell.unionCache publicSeed table z.2.1.cache)

end SlhDsaSecurity.InputBullet

import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.SharedJoin

/-!
# What the ordering slot can and cannot also buy

The question the ledger turns on: the ordering term is a union bound over
`SharedJoin.recordMessageClass`, one unit of `2 ^ -128` per entry. Can the same slot also pay
for the seed witness, when that witness is a message-class entry?

**Per entry the two events are different, and the merged event costs two units.** For an entry
`Hashing.messageInput r pk m` of the record:

* the ordering term's per-entry event is that `r` is the truncation of the oracle's answer at
  `Hashing.randomizerInput SK.prf PK.seed m` — the entry becomes disclosing at a draw the run
  makes later;
* the seed witness's per-entry event is that `r` **is** `SK.prf`, by the FIPS 205 format
  identity — a guess at the secret, decided by the seed and not by any answer.

Both are "`r` hits a fixed digest", at the same rate, but at **two different digests**. Their
disjunction is `r` hitting either, and `prob_two_targets_le` below is what that costs: two
units, not one. The two coincide only when the randomiser answer for `m` truncates to the seed,
which is `RandomizerGate.RandomizerHitsSeed` — itself a separately charged event, so the
coincidence cannot be assumed.

**So the slot does not cover both**, and the honest ledger needs `2 · E[card recordMessageClass]`
where it now needs one. That is a fact about the budget rather than a choice, and the budget
does not admit it: `SharedJoin.card_parts_le_record` bounds
`card recordAiming + card recordMessageClass` by the record, and nothing bounds
`card recordMessageClass` below the record — an adversary whose every query is a message input
aiming nowhere has `card recordMessageClass = counts.work`, at which point `2 · work` exceeds
the `q - 2 ^ subtreeHeight` the four slots share.

**What this does not say.** The seed witnesses that lie *outside* the message class are
unaffected: `RecordColumn.card_three_parts_le_record` shows the subtracted third part fits with
room to spare and no walk condition. The cost is confined to witnesses that are message-class
entries, which exist only through the format identity.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordSlot

open Security


/-- **Two targets cost two units.** The merged per-entry event — this entry's randomiser field
hits either the disclosing truncation or the secret seed — is a guess at a two-element set, and
a union bound is all that is available because the two targets are independent of each other. -/
theorem prob_two_targets_le (first second : Digest) :
    Pr[fun drawn : Digest => first = drawn ∨ second = drawn |
      ($ᵗ Digest : ProbComp Digest)] ≤ 2 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_or_le _ _ _) ?_
  rw [SecretGuessCharge.prob_single_guess first, SecretGuessCharge.prob_single_guess second,
    ENNReal.div_add_div_same]
  norm_num

/-- **And one target costs one**, which is what the ordering slot already pays. The two
statements side by side are the whole of the unit question: the slot buys one digest's worth of
rate per entry, and the merged event names two digests. -/
theorem prob_one_target_eq (target : Digest) :
    Pr[fun drawn : Digest => target = drawn | ($ᵗ Digest : ProbComp Digest)] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  SecretGuessCharge.prob_single_guess target

/-! ## The filing fix does not close it, and the record it is stated about is the other one

`ObligationShapes`' closing paragraph proposes that this case needs no unit at all: *the
recorder files on fresh draws, and this draw was not the adversary's*, so it is a bookkeeping
gap rather than a probability one. Two things are wrong with applying that here, and both are
checkable rather than arguable.

**The record this charge is read against is not freshness-guarded.**
`RandomiserRecord.chargedRecord` is `result.1.1.2`, written by
`RecordedQueries.recordedAdversaryImpl`, which is `QueryImpl.withAddCost` at the cost function
`fun input => (Counts.single .hash (hashCost input), recordOf input)`. By
`WriterState.run_withAddCost_run` that cost is added **unconditionally** — the equation mentions
neither the state nor the cache — so a repeated query is filed like a first one. The positive
control is `SharedJoin.card_record_eq_work`, and it is an **equality**:
`Multiset.card result.1.1.2 = result.1.1.1.counts.work`. If repeats were filtered the card would
fall strictly below the work count on any run that repeats a query, and the equality would be
false.

The freshness guard the paragraph describes is real but belongs to `RecorderView.appendedOf`,
whose two branches both test `CacheView.cacheOf state.1 input = none`. That is the split
recorder, not the cost writer's record. **The paragraph is a true statement about a different
object.**

**And implementing it would close only half the case.** The paragraph's situation is that the
signer queried the forgery's digest input first. An adversary need not wait for the signer: it
can query `Hashing.messageInput x pk m` for a guessed `x` before asking for any signature. That
query is fresh, so a freshness-guarded record files it too, and if `x` is `SK.prf` the entry is a
seed witness of exactly the kind this file is about. So the filing fix removes the signer-first
sub-case and leaves the adversary-first one, which is the one a `q`-shaped charge is counting in
the first place.

**So the second unit is still needed and the overflow stands.** Recorded here rather than left
to be rediscovered, since the paragraph reads as though it settles the case.
-/

/-! ## The answer half cannot pay for it either, on two independent grounds

The last place a payer could have been hiding. It is not there.

**Structurally the answer half is relieved of this event, not charged for it.**
`Obligations.AnswerChargedAt` bounds `AnswerBad ∧ ¬ late`, and at this tail `late` is
`FinalAssembly.lateOrSeed`, which *contains* `AnswerCoverage.ForgerySeedRandomised`. So the seed
event is excluded from the answer half's event by hypothesis — that exclusion is precisely why
the shared half carries it. Asking the answer half to pay would mean restating it at
`late := LateProbes.Ordering`, which is the door `CarrierTail.answerChargedLate_carrier_of_bound`
provides and whose hypothesis nobody has discharged.

**And budgetarily there is nothing to pay with.** The answer half's allowance is
`(q : ℝ≥0∞) / 2 ^ 128 + answerDefect`: one `q`, already spent on its own event, with
`answerDefect` the constant part. `Target`'s own line says what follows:

> *The `q` coefficient has no margin at all: the same `Nat` line is `2 * q` on the right and
> `q + q` on the left, so the two halves have one budget each and a third `q`-proportional term
> cannot be added. Constants can, up to the margin.*

Two `q`-proportional terms are allowed and two are used. The second unit per message-class entry
is a third, bounded by `E[card recordMessageClass] ≤ counts.work ≤ q - 2 ^ subtreeHeight` and by
nothing smaller — nothing in the development bounds the message class below the whole record, and
an adversary all of whose queries are message inputs aiming nowhere attains it.

**So the arithmetic of the shortfall is `3q` where the line allows `2q`**, a factor of `3/2`,
which is `log2 (3/2) ≈ 0.585` of a bit. On this route the honest statement is therefore about
`126.4` bits rather than `127` — a smaller number, not a longer proof.

This is recorded here rather than left as an absence because every other avenue is closed above,
and an unexamined quarter reads the same as an examined one once the file is quiet.
-/

/-! ## Can the message class be bounded below the record? What is actually attainable

The last numerical escape: a bound `card recordMessageClass ≤ c · card recordOf` with `c < 1`
would shrink the overflow. The theorem below says what stands in the way, and it is not a
belief — **the filter is the identity whenever every recorded input is a message input**, so a
strict bound would have to rule such records out.

On a good walk the aiming conjunct is free: `SharedJoin.not_aimsSomewhere_messageInput` says a
message input at the walk's key aims nowhere. So `recordMessageClass` is *exactly* the message
inputs of the record, and the only question is how many of the record's entries the adversary can
make message inputs.

**And the honest answer is: all of its own, but not all of the record.** The record is the
adversary's hash queries *and the verifier's*, by `SharedJoin.card_record_eq_work`
(`work = hash + verification`). The adversary can make every one of its own queries a message
input — `CombinedCharge.IsMessageInput pk (Hashing.messageInput r pk m)` holds for any `r` and
`m`, and the public key is its input — but the verifier also queries Merkle and FORS inputs,
which are structural and not message inputs. So the attainable value of
`card recordMessageClass` is `card recordOf` **less the verifier's own structural queries**,
which is a constant of the scheme and not a fraction of `q`.

**So no bound of the form `c · card recordOf` with `c < 1` is available, and the overflow stays
`q`-proportional.** Subtracting a constant from a `q`-sized term changes no coefficient. This
sharpens the previous reading — strict equality is *not* attainable, and it does not matter,
because the escape needed a factor and only a constant is on offer.
-/

/-- **The message class is the whole record when the record is all message inputs.** The
hypothesis is what a strict bound would have to refute, stated so that it can be looked at
rather than assumed away. -/
theorem recordMessageClass_eq_record_of_all (adversary : Adversary)
    {pair : SharedJoin.RecordedPair}
    (hpair : pair ∈ support (RandomiserRecord.recordedPairedRun adversary))
    (hgood : Target.GoodWalk pair.1)
    (hall : ∀ input ∈ SharedJoin.recordOf pair, CombinedCharge.IsMessageInput
      (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2) input) :
    SharedJoin.recordMessageClass pair = SharedJoin.recordOf pair := by
  classical
  obtain ⟨hwalk, -⟩ := SharedJoin.mem_support_recordedPairedRun hpair
  rw [SharedJoin.recordMessageClass]
  refine Multiset.filter_eq_self.mpr fun input hmem => ?_
  exact ⟨hall input hmem,
    SharedJoin.not_aimsSomewhere_messageInput hwalk hgood input (hall input hmem)⟩

/-- **And the adversary can name a message input at will**, the public key being its own input.
So the hypothesis above is not exotic: it asks only that the adversary spend its queries on a
shape it chooses. -/
theorem isMessageInput_messageInput (pk : PublicKey) (randomizer : Digest) (message : Bytes) :
    CombinedCharge.IsMessageInput pk (Hashing.messageInput randomizer pk message) :=
  ⟨randomizer, message, rfl⟩

/-! ## Is the factor slack, or is it the attack's own?

A union bound is an upper bound on our ignorance, so a proof that loses a factor does not by
itself say an adversary gains one. Two things say this one is not slack.

**The two targets are disjoint**, so nothing is double-counted and the union bound loses
nothing to overlap: `two_targets_disjoint` below. Disjoint events' probabilities add exactly, so
the per-entry cost really is two units whenever the two targets differ, and they differ except
on `RandomizerGate.RandomizerHitsSeed`, which has its own slot.

**And one oracle call stakes both guesses.** `FramingLeak.randomizerInput_eq_messageInput` makes
a single query at `prf ‖ PK.seed ‖ PK.root ‖ m` simultaneously a `PRF_msg` query — staking a
guess at `SK.prf` — and an `H_msg` query — staking a guess at the message digest. The adversary
can check either hit against a published randomiser. So the two staked guesses per query are the
shared oracle's doing, not the proof's.

**That is also exactly what the proposed attack's arithmetic says.**
`SharedOracleArithmetic.proposedLowerBound`'s leading term is `2 * (work - setup) / wordSpace` —
two guesses per query — and `proposed_bound_exceeds_target` certifies the total exceeds
`2 * work / wordSpace`, which is `work / 2 ^ 127`. What that file does **not** claim, in its own
words, is that any concrete adversary achieves it: *"the connection to the actual experiment is
a separate obligation."* So the arithmetic for the loss being real is in the tree and the link
to the experiment is not.
-/

/-- **The two per-entry targets are disjoint**, so the union bound over them loses nothing to
overlap and the per-entry cost is exactly two units when the targets differ. -/
theorem two_targets_disjoint (first second drawn : Digest) (hne : first ≠ second) :
    ¬ (first = drawn ∧ second = drawn) := by
  rintro ⟨hfirst, hsecond⟩
  exact hne (hfirst.trans hsecond.symm)

end SlhDsaSecurity.RecordSlot

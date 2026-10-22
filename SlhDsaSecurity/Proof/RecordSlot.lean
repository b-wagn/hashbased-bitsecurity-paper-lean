import SlhDsaSecurity.Proof.SecretGuessCharge

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

end SlhDsaSecurity.RecordSlot

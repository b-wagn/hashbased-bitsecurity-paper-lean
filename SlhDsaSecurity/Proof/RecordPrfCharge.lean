import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.RandomiserRecord

/-!
# What the record charge actually spends

`RandomiserRecord.RecordMeetsPrfClass` is the last quantity in the ledger that is assumed rather
than derived: `ObligationShapes.sharedChargedLate_of_parts_record` takes it at `qp` units and
nobody has shown any particular number is enough. This file answers the one question that
decides the shape — **does the thing being paid for grow with `q`?** — and the answer is yes.

**One recorded input is one guess at `SK.prf`.** `RandomizerGate.PrfClass prfSeed input` says
`input` *is* `Hashing.randomizerInput prfSeed seed message` for some seed and message, and
`Hashing.randomizerInput_injective` makes the seed a function of the input: for a fixed input
there is at most one `prfSeed` in the class. So each recorded input rules in exactly one value
of a uniformly drawn secret, and the union bound over the record is the whole accounting.

**So the charge is `card`-shaped, and `card` is `q`-shaped.**
`RandomiserRecord.card_chargedRecord_le` bounds the record by `counts.work`, and
`RecordedBudget.work_add_pow_le_of_budget_tail` bounds `work + 2 ^ subtreeHeight` by `q`. There
is no constant here: a numeral `qp` asserts the adversary makes at most `qp` recorded queries.

**Where that leaves `qp := 251`.** With `subtreeHeight = 9`, the constant column is
`claims + defectUnits ≤ 512`; at the proved defect allowance of two units that is
`claims ≤ 510`, and `259 + qp ≤ claims` leaves `qp ≤ 251`. So **251 is the headroom of the
constant column and not a bound on anything** — which is what it was reported as. The same name
`qp` in `SharedJoin.prob_sharedBad_le` sits in the *`q`-shaped* sum
`qc + qp + qm + qs ≤ q - 2 ^ subtreeHeight`, where a `Nat` is the right shape because the sum is
allowed to be `q`-sized. The slot changed column when it moved between the two files, and
nothing in the types notices, because it is a `Nat` in both.

**What is proved here and what is not.** The bound below is in the **blind order**: the record
is fixed and the secret is drawn afterwards. In the game the secret is drawn first and the
record depends on it, so this does not yet charge the real experiment. That gap is already
recorded twice — `SecretGuessCharge`'s header and `BlindKey.hit_probability_le` — and its own
conclusion is the one to keep: *the key-guessing accounting is finished twice over, and the gap
is solely in the rewriting that makes the transcript key-independent.* This file adds the third
instance of the accounting and moves nothing on the coupling; what it settles is the **shape**,
which is what the ledger needs before it needs the coupling.

`RecordedTail.recordedTail` is made locally irreducible for the last statement, exactly as
`RandomiserRecord` does: it unfolds to the whole game and nothing here needs to look inside it.
Without that, both the elaborator and `constructorNameAsVariable` try to whnf it and time out —
the same symptom as at `CarrierTailRecordings`, with the honest fix available here because the
neighbouring file had already found it.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordPrfCharge

open Security RandomizerGate RandomiserRecord

/-- **A fixed input rules in at most one seed.** The class names the seed it is at, so an input
of the class for two seeds forces them equal. -/
theorem prob_prfClass_single_le (input : Bytes) :
    Pr[fun prfSeed : Digest => PrfClass prfSeed input | ($ᵗ Digest : ProbComp Digest)] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hex : ∃ prfSeed : Digest, PrfClass prfSeed input
  · obtain ⟨candidate, hcandidate⟩ := hex
    refine le_of_le_of_eq (probEvent_mono (q := fun prfSeed : Digest => candidate = prfSeed)
      fun prfSeed _ hbad => ?_) (SecretGuessCharge.prob_single_guess candidate)
    obtain ⟨seed, message, hmessage⟩ := hbad
    obtain ⟨other, otherMessage, hother⟩ := hcandidate
    exact (Hashing.randomizerInput_injective (hother.symm.trans hmessage)).1
  · rw [probEvent_eq_zero fun prfSeed _ hbad => hex ⟨prfSeed, hbad⟩]
    exact zero_le

open scoped Classical in
/-- **The record charge, in the blind order.** A record of `card` inputs stakes `card` guesses at
a secret drawn afterwards. -/
theorem prob_recordMeetsPrfClass_blind (inputs : Finset Bytes) :
    Pr[fun prfSeed : Digest => ∃ input ∈ inputs, PrfClass prfSeed input |
      ($ᵗ Digest : ProbComp Digest)] ≤ inputs.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_exists_finset_le_sum inputs _ _) ?_
  calc ∑ input ∈ inputs,
        Pr[fun prfSeed : Digest => PrfClass prfSeed input | ($ᵗ Digest : ProbComp Digest)]
      ≤ ∑ _input ∈ inputs, 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_le_sum fun input _ => prob_prfClass_single_le input
    _ = inputs.card * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ inputs.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := le_of_eq (by rw [mul_one_div])

-- As in `RandomiserRecord`: the tail unfolds to the whole game, and nothing below needs to
-- look inside it.
attribute [local irreducible] RecordedTail.recordedTail

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **And at the run's own record, the count is the work.** This is the statement that settles
the shape: the right-hand side is the run's hash count, which the budget bounds by
`q - 2 ^ subtreeHeight`, so no element of `Nat` bounds it. -/
theorem prob_recordMeetsPrfClass_blind_le_work (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    {result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk)) :
    Pr[fun prfSeed : Digest => RecordMeetsPrfClass prfSeed result |
      ($ᵗ Digest : ProbComp Digest)] ≤
      ((result.1.1.1.counts.work : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (prob_recordMeetsPrfClass_blind (chargedRecord result))
    (ENNReal.div_le_div_right
      (Nat.cast_le.mpr (card_chargedRecord_le adversary hresult)) _)

end SlhDsaSecurity.RecordPrfCharge

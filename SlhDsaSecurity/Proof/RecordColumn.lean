import SlhDsaSecurity.Proof.ObligationShapes
import SlhDsaSecurity.Proof.RecordPrfCharge

/-!
# The record charge, in the column it belongs to

`RecordPrfCharge` settled the shape: the record charge grows with `q`, because one recorded
input is one guess at `SK.prf` and the record is the run's own work.
`ObligationShapes.sharedChargedLate_of_parts_record` spends it from `claims`, through
`259 + qp ≤ claims`, and `claims` is the **constant** column — capped by
`claims + defectUnits ≤ 2 ^ subtreeHeight`. This file is the same assembly with the charge in
the `q`-shaped column, which is where `SharedJoin.prob_sharedBad_le` already had it, inside
`qc + qp + qm + qs ≤ q - 2 ^ subtreeHeight`.

**The two columns look the same in the types and are different claims.** `qp : Nat` inside the
`q`-shaped sum is right, because the sum is allowed to be `q`-sized; `qp : Nat` added to
`claims` asserts a constant. Nothing distinguishes them but where they are added, which is why
asking *does the event grow with `q`?* did not catch this: the answer was recorded in a slot
whose column nobody checked.

**What changes and what does not.** `hclaims` loses its `qp` and becomes `259 ≤ claims`, so the
constant column pays for the input bullet's `259` and nothing else. In exchange `hrecord` is
stated against an expectation of a record part rather than a numeral, and a new hypothesis
`hparts` says the three parts share the budget. That last is the price of the column and is the
subject of `SharedJoin.card_parts_le_record`'s successor; it is a counting fact about one
record, not a charge, and it is stated here rather than assumed inside.

**The seed row's status, stated once so it is not mistaken again.** Shape known and `q`-shaped;
column fixed here; magnitude still blocked on the coupling that makes the real transcript
key-independent, since `RecordPrfCharge` proves its bound in the blind order only.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordColumn

open Security WarmedGame Target SharedJoin RoutedSplit

/-- The third part of the record: its entries that are `PRF_msg` inputs at the real seed. -/
noncomputable def recordPrfClass (pair : SharedJoin.RecordedPair) : Multiset Bytes :=
  open scoped Classical in
  (SharedJoin.recordOf pair).filter (RandomizerGate.PrfClass pair.1.1.1.2.1)

/-- **The charge's event is the third part being non-empty.** So a bound on the part's
cardinality is a bound on the charge, by `RecordPrfCharge`'s accounting. -/
theorem recordMeetsPrfClass_iff (pair : SharedJoin.RecordedPair) :
    RandomiserRecord.RecordMeetsPrfClass pair.1.1.1.2.1 pair.2 ↔
      ∃ input ∈ recordPrfClass pair, RandomizerGate.PrfClass pair.1.1.1.2.1 input := by
  classical
  constructor
  · rintro ⟨input, hmem, hclass⟩
    exact ⟨input, Multiset.mem_filter.mpr ⟨Multiset.mem_toFinset.mp hmem, hclass⟩, hclass⟩
  · rintro ⟨input, hmem, hclass⟩
    exact ⟨input, Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp hmem).1, hclass⟩

set_option maxHeartbeats 1000000 in
/-- **The shared obligation with the record charge in the `q`-shaped column.**

`hclaims` is `259 ≤ claims`: the constant column pays the input bullet's `259` and nothing
else. `hrecord` is an expectation, not a numeral. `hparts` is the counting fact that the three
parts fit in one record's worth of budget, which is what the column costs. -/
theorem sharedChargedLate_of_parts_record_at (fused : LateProbes.FusedTail)
    (claims : Nat) (late seedEvent : LateProbes.SplitPair → Prop)
    (hclaims : 259 ≤ claims)
    (hlate : ∀ pair : LateProbes.SplitPair, late pair →
      LateProbes.Ordering pair ∨ seedEvent pair)
    (hforget : ∀ adversary : Adversary, LateProbes.ForgetsTo fused adversary)
    (hordering : ∀ adversary : Adversary,
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ LateProbes.Ordering pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBulletAt fused adversary LateProbes.Ordering)
    (hrecord : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ seedEvent pair |
          LateProbes.pairedOf fused adversary] ≤
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (recordPrfClass (LateProbes.forgetRecordings pair))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hparts : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair => Multiset.card (recordPrfClass (LateProbes.forgetRecordings pair))) ≤
        ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞)) :
    Obligations.SharedChargedLate claims fused FinalAssembly.forgetFused late := by
  classical
  intro q adversary _ hbudget
  have hordering := hordering adversary
  refine le_trans (probEvent_mono (q := fun pair : LateProbes.SplitPair =>
    (GoodWalk pair.1 ∧ InputBad (SharedAssembly.splitTraceOf pair) ∧
        ¬ LateProbes.Ordering pair) ∨
      ((GoodWalk pair.1 ∧ LateProbes.Ordering pair) ∨
        (GoodWalk pair.1 ∧ seedEvent pair))) ?_) ?_
  · rintro pair - ⟨hgood, hshared | hlatePair⟩
    · exact (SharedJoin.cover_of_em
        (fun pair : LateProbes.SplitPair => InputBad (SharedAssembly.splitTraceOf pair))
        LateProbes.Ordering pair hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord =>
          Or.inl ⟨hgood, hord⟩
    · exact Or.inr ((hlate pair hlatePair).imp (fun hord => ⟨hgood, hord⟩)
        fun hseeded => ⟨hgood, hseeded⟩)
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget)
    (le_trans (probEvent_or_le _ _ _)
      (add_le_add hordering (hrecord q adversary hbudget)))) ?_
  rw [← add_assoc, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
        ((259 : Nat) : ℝ≥0∞) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair)))) +
        ClassExpectation.expected (LateProbes.pairedOf fused adversary)
          (fun pair => Multiset.card (recordPrfClass (LateProbes.forgetRecordings pair)))
      = (ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf fused adversary)
            (fun pair => Multiset.card (recordPrfClass (LateProbes.forgetRecordings pair)))) +
          ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((claims : Nat) : ℝ≥0∞) :=
        add_le_add (hparts q adversary hbudget) (Nat.cast_le.mpr hclaims)
    _ = ((q - 2 ^ subtreeHeight + claims : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The price of the column, and why it is not a disjointness lemma

`hparts` is what the `q`-shaped column costs, and the obvious way to pay it — the three parts
are disjoint, so they fit in one record — **is false**, unconditionally.

`FramingLeak.randomizerInput_eq_messageInput` is an identity of the FIPS 205 byte formats with
no hypothesis: `PRF_msg(prf, PK.seed, PK.root ‖ m)` and `H_msg(prf, PK.seed, PK.root, m)` are
the same bytes. So **every message input whose randomiser field is `SK.prf` is already in
`PrfClass SK.prf`**, and `recordPrfClass` meets `recordMessageClass` exactly there. That is
`prfClass_messageInput_prf` below, and it is one line because the leak is structural rather
than probabilistic — `GoodWalk` does not exclude it, since the identity never mentions the
public seed.

**So the overlap is the charged event itself.** A record entry in both parts is a message input
whose randomiser field is the secret seed, which is precisely a witness for
`RandomiserRecord.RecordMeetsPrfClass`. Subtracting it away, as `recordMessageClass` subtracts
`AimsSomewhere`, makes the three parts fit — that is `card_three_parts_le_record` — but it moves
the witnesses out of the part the charge is read at, so the subtracted form does not discharge
`hrecord` on its own. What is left over is a message-class entry that guesses the seed, and it
has to be accounted for somewhere; `recordMessageClass`'s own slot is already spent on the
ordering defect.

Both halves are stated here so the next reader does not spend the afternoon proving a
disjointness that cannot hold. -/

/-- **The overlap is real and needs no hypothesis.** A message input at the secret seed *is* a
`PRF_msg` input at that seed, by the byte-format identity. -/
theorem prfClass_messageInput_prf (prfSeed : Digest) (pk : PublicKey) (message : Bytes) :
    RandomizerGate.PrfClass prfSeed (Hashing.messageInput prfSeed pk message) :=
  ⟨pk.seed, _, (FramingLeak.randomizerInput_eq_messageInput prfSeed pk message).symm⟩

/-- The third part with the other two subtracted, so that the three are disjoint by
construction — the device `recordMessageClass` already uses against `recordAiming`. -/
noncomputable def recordPrfOnly (pair : SharedJoin.RecordedPair) : Multiset Bytes :=
  open scoped Classical in
  (SharedJoin.recordOf pair).filter fun input =>
    RandomizerGate.PrfClass pair.1.1.1.2.1 input ∧
      ¬ AimsSomewhere pair.1.1.1.2.2 input ∧
        ¬ CombinedCharge.IsMessageInput
          (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2) input

open scoped Classical in
/-- **The three subtracted parts fit inside the record**, on every run and with no `GoodWalk`.
The same device as `SharedJoin.card_parts_le_record`, one filter further. -/
theorem card_three_parts_le_record (pair : SharedJoin.RecordedPair) :
    Multiset.card (SharedJoin.recordAiming pair) +
        Multiset.card (SharedJoin.recordMessageClass pair) +
      Multiset.card (recordPrfOnly pair) ≤ Multiset.card (SharedJoin.recordOf pair) := by
  classical
  have hfirst : ∀ input ∈ SharedJoin.recordOf pair,
      ¬ (AimsSomewhere pair.1.1.1.2.2 input ∧
        (CombinedCharge.IsMessageInput
            (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
            input ∧
          ¬ AimsSomewhere pair.1.1.1.2.2 input)) := by
    rintro input - ⟨haims, -, hnot⟩
    exact hnot haims
  have hsecond : ∀ input ∈ SharedJoin.recordOf pair,
      ¬ ((AimsSomewhere pair.1.1.1.2.2 input ∨
          (CombinedCharge.IsMessageInput
              (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
              input ∧
            ¬ AimsSomewhere pair.1.1.1.2.2 input)) ∧
        (RandomizerGate.PrfClass pair.1.1.1.2.1 input ∧
          ¬ AimsSomewhere pair.1.1.1.2.2 input ∧
            ¬ CombinedCharge.IsMessageInput
              (SplitCharged.generatedKey pair.1.1.1.1 pair.1.1.1.2.1 pair.1.1.1.2.2 pair.1.2)
              input)) := by
    rintro input - ⟨hleft, -, hnotAims, hnotMessage⟩
    rcases hleft with haims | ⟨hmessage, -⟩
    · exact hnotAims haims
    · exact hnotMessage hmessage
  rw [SharedJoin.recordAiming, SharedJoin.recordMessageClass, recordPrfOnly,
    ← Multiset.card_add, ← Multiset.card_add, Multiset.filter_add_filter,
    Multiset.filter_eq_nil.mpr hfirst, add_zero, Multiset.filter_add_filter,
    Multiset.filter_eq_nil.mpr hsecond, add_zero]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

end SlhDsaSecurity.RecordColumn

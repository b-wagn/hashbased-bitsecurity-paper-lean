import SlhDsaSecurity.Proof.LateProvenance
import SlhDsaSecurity.Proof.ProbeContainment

/-!
# The shared obligation, from the pieces that exist

`AnswerJoin` did this for the answer half: take each piece in the shape its owner produces, add
them, and let a mismatch surface here rather than at assembly. This is the same for the shared
half, and there is only one piece left to take as a hypothesis — the input half's bullet. The
ordering term is discharged rather than assumed, and the cover is free.

**The whole shared side now reads at the pair that carries the recordings.** It has to: the
ordering defect is not a predicate of the recorded pair, so `¬ ordering` — which is what the
input half's charge is conditioned on — is not one either, and the two halves have to meet on
one object. `LateProbes.probEvent_forget` is what makes that cost nothing for everything else:
every event the join already had is a predicate of the recorded pair, so it keeps its
probability exactly, and every count it already had keeps its expectation.

So the input half's bullet is the one it has pinned with three readings moved: the run is the
one the ordering term is read at, the pair it reads the record and the trace from is that pair's
image under `LateProbes.forgetRecordings`, and `ordering` is a predicate of the larger pair. Its
own argument does not have to change shape for that — `¬ ordering` is used pointwise on the
support, and the support of the larger run maps onto the smaller one.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SharedAssembly

open Security WarmedGame RoutedSplit Target ClassExpectation SharedJoin RandomiserRecord
  LateProbes

/-- The trace the shared side's events read, at the pair that carries the recordings. -/
abbrev splitTraceOf (pair : SplitPair) : RoutedSplit.Trace :=
  SharedJoin.recordedTraceOf (forgetRecordings pair)

/-- **The input half's bullet at whatever tail the assembly is run on.** Nothing in the bullet
is about which tail produced the pair: the event, the aiming count and the `259` all read the
pair, and the tail enters only as the measure. So the statement is parametric and the tail the
development currently assembles at is one instance of it, which is what lets a half proved at
one presentation meet an assembly stated at another by `exact`. -/
def InputBulletAt (fused : LateProbes.FusedTail) (adversary : Adversary)
    (ordering : SplitPair → Prop) : Prop :=
  Pr[fun pair : SplitPair => GoodWalk pair.1 ∧ InputBad (splitTraceOf pair) ∧ ¬ ordering pair |
      pairedOf fused adversary] ≤
    (expected (pairedOf fused adversary)
        (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) +
      ((259 : Nat) : ℝ≥0∞)) / ((2 ^ 128 : Nat) : ℝ≥0∞)

/-- **The input half's bullet, at the pair the ordering term is read at.** This is
`ProbeContainment.InputBullet` with its three recorded-pair readings taken at
`LateProbes.forgetRecordings pair` and its `ordering` a predicate of the larger pair. -/
def InputBullet (adversary : Adversary) (ordering : SplitPair → Prop) : Prop :=
  InputBulletAt FusedCoverage.fusedTail adversary ordering

/-- **The named bullet is the parametric one at the fused tail**, definitionally, so a producer
or a consumer of either is one of the other with no adapter. -/
theorem inputBullet_eq_at (adversary : Adversary) (ordering : SplitPair → Prop) :
    InputBullet adversary ordering =
      InputBulletAt FusedCoverage.fusedTail adversary ordering := rfl

/-- **What the move costs, exactly.** An ordering event that *is* a predicate of the recorded
pair needs no restatement at all: the bullet as the input half has pinned it gives this one by
transport, because every reading in it is of the recorded pair and transport is free for those.
So the three readings are the whole of the change, and the only thing that forces it is that the
ordering defect is not such a predicate. -/
theorem inputBullet_of_recorded (adversary : Adversary) (ordering : RecordedPair → Prop)
    (hbullet : ProbeContainment.InputBullet adversary ordering) :
    InputBullet adversary (fun pair => ordering (forgetRecordings pair)) := by
  classical
  have hprob : Pr[fun pair : SplitPair => GoodWalk pair.1 ∧ InputBad (splitTraceOf pair) ∧
        ¬ ordering (forgetRecordings pair) | pairedOf FusedCoverage.fusedTail adversary] =
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
        ¬ ordering pair | recordedPairedRun adversary] :=
    probEvent_forget (FusedCoverage.forgetsTo adversary)
      (fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) ∧
        ¬ ordering pair)
  have hcount : expected (pairedOf FusedCoverage.fusedTail adversary)
        (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) =
      expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordAiming pair)) :=
    expected_forget (FusedCoverage.forgetsTo adversary)
      (fun pair : RecordedPair => Multiset.card (recordAiming pair))
  rw [InputBullet, InputBulletAt, hprob, hcount]
  exact hbullet

/-- **The input half's containment survives the move untouched.** A supported pair of the larger
run forgets to a supported pair of the smaller, so a `SharedJoin.ProbesIn` proved there applies
here by one application. Only the bullet is restated; what sits under it is not. -/
theorem probesIn_forget (part probes : RecordedPair → Multiset Bytes) (adversary : Adversary)
    (hprobes : ProbesIn part probes adversary) :
    ∀ pair ∈ support (pairedOf FusedCoverage.fusedTail adversary),
      probes (forgetRecordings pair) ≤ part (forgetRecordings pair) :=
  fun _ hpair => hprobes _ (mem_support_forget (FusedCoverage.forgetsTo adversary) hpair)

/-! ## The two counts still fit the budget

They are two parts of one record and disjoint by construction, so the join's own bound applies
to them at the image pair, and the expectation is taken at the larger run. -/

open scoped Classical in
/-- **The budget split at any tail that forgets to the game.** The pathwise fact
`card_parts_le_budget` is about the recorded pair, so all the tail supplies is that its own pairs
forget to supported ones — which is exactly `LateProbes.ForgetsTo`. -/
theorem expected_parts_le_budget_at (fused : LateProbes.FusedTail) (q : Nat)
    (adversary : Adversary) (hforget : LateProbes.ForgetsTo fused adversary)
    (hbudget : HasTotalBudget adversary q) :
    expected (pairedOf fused adversary)
        (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) +
      expected (pairedOf fused adversary)
        (fun pair => Multiset.card (recordMessageClass (forgetRecordings pair))) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
  classical
  rw [← expected_add]
  exact expected_le_of_le _ _ _ fun pair hpair =>
    card_parts_le_budget adversary q hbudget (mem_support_forget hforget hpair)

open scoped Classical in
theorem expected_parts_le_budget (q : Nat) (adversary : Adversary)
    (hbudget : HasTotalBudget adversary q) :
    expected (pairedOf FusedCoverage.fusedTail adversary)
        (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) +
      expected (pairedOf FusedCoverage.fusedTail adversary)
        (fun pair => Multiset.card (recordMessageClass (forgetRecordings pair))) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) :=
  expected_parts_le_budget_at FusedCoverage.fusedTail q adversary
    (FusedCoverage.forgetsTo adversary) hbudget

/-! ## The assembly -/

set_option maxHeartbeats 1000000 in
/-- **The shared obligation, from the input half's bullet and nothing else.** The ordering term
is `LateProbes.prob_ordering_le` with its containment discharged by provenance; the cover is
excluded middle; the arithmetic is the join's own. -/
theorem sharedCharged_of_parts
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary) :
    Obligations.SharedCharged := by
  classical
  intro q adversary _ hbudget
  have hforget := FusedCoverage.forgetsTo adversary
  have hprobes := probes_le_recordMessageClass hforget (FusedCoverage.isRecorderRun adversary)
    (LateProvenance.hrecord_of_signerDigestFree adversary (hsigner adversary))
  have hordering := prob_ordering_le (FusedCoverage.isRecorderRun adversary) hprobes
  rw [probEvent_pairedRun_eq, ← probEvent_forget hforget]
  refine le_trans (probEvent_mono (q := fun pair : SplitPair =>
    (GoodWalk pair.1 ∧ InputBad (splitTraceOf pair) ∧ ¬ LateProbes.Ordering pair) ∨
      (GoodWalk pair.1 ∧ LateProbes.Ordering pair)) ?_) ?_
  · rintro pair hpair ⟨hgood, hshared⟩
    exact (cover_of_em (fun pair : SplitPair => InputBad (splitTraceOf pair))
      LateProbes.Ordering pair hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord => ⟨hgood, hord⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget) hordering) ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc expected (pairedOf FusedCoverage.fusedTail adversary)
          (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) +
        ((259 : Nat) : ℝ≥0∞) +
        expected (pairedOf FusedCoverage.fusedTail adversary)
          (fun pair => Multiset.card (recordMessageClass (forgetRecordings pair)))
      = expected (pairedOf FusedCoverage.fusedTail adversary)
            (fun pair => Multiset.card (recordAiming (forgetRecordings pair))) +
          expected (pairedOf FusedCoverage.fusedTail adversary)
            (fun pair => Multiset.card (recordMessageClass (forgetRecordings pair))) +
          ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add (expected_parts_le_budget q adversary hbudget) le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

end SlhDsaSecurity.SharedAssembly

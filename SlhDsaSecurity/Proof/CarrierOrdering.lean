import SlhDsaSecurity.Proof.CarrierCharge
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.BracketedOrdering

/-!
# The ordering defect's per-walk bound, at the carrier tail

The last piece. `BracketedOrdering.prob_ordering_le` takes the charge read walk by walk;
`CarrierCharge.prob_fired_le_threeStage` is that charge, and `CarrierTail.carrierTail` is already
written in the three-stage shape the charge is stated at — so this file is the match-up and the
arithmetic, and no induction.

**The test the tail is run at is `chargedKeepAt`**, the carrier's own test together with the
exclusion the step bound needs. `CarrierCharge.chargedRightKeep` says why that is the right
shape rather than a workaround; here it is simply the test, and `hright` below is the projection
that carries every fact already proved about `AnswerCarrier.carrierRightKeep` across.

**Three readings line up by definition and one by `GoodWalk`.** `LateProbes.Ordering` at the
forgotten pair *is* `CarrierCharge.Fired` at the carrier state, because both are
`LateRate.Served.Fired` of the cache-side disclosure read at `BracketedRun.forgetCarrier`; the
potential and the gauge at the tail's start are both zero, because the tail starts with both
recordings empty. What needs the walk to be good is the **gauge against the probe count**:
`LateProbes.probes` is the target recording's inputs on a good walk and empty off one, so the
two agree exactly where the charge is read and nowhere else.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierOrdering

open Security BracketedRun CarrierTail CarrierFiles ClassExpectation PhaseFusion
  RecordedQueries

/-- **The test the carrier tail is run at**: the carrier's own, and not already disclosing. -/
noncomputable def chargedKeepAt (walk : Walk) : Bytes → HandlerCarrier.State → Prop :=
  CarrierCharge.chargedRightKeep walk.1.1.2.1 (keyAt walk) (AnswerCarrier.carrierRightKeep walk)

/-- **It is the carrier's test**, so `hrecord` and both recording invariants apply to it. -/
theorem chargedKeepAt_carrierRightKeep (walk : Walk) (input : Bytes)
    (view : HandlerCarrier.State) (hkeep : chargedKeepAt walk input view) :
    AnswerCarrier.carrierRightKeep walk input view := hkeep.1

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The ordering defect at one walk, charged against the probe count.** -/
theorem prob_ordering_perWalk (adversary : Adversary) (walk : Walk)
    (hgood : Target.GoodWalk walk) :
    Pr[fun result => LateProbes.Ordering (walk, result) |
        carrierTail chargedKeepAt adversary walk] ≤
      expected (carrierTail chargedKeepAt adversary walk)
          (fun result => Multiset.card (LateProbes.probes (walk, result))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hmain := CarrierCharge.prob_fired_le_threeStage (keyAt walk)
    (chargedKeepAt walk) walk.1.1.2.1 (keyAt walk)
    (LateCharge.Spent walk.1.1.2.1 (keyAt walk)) LateRate.rate
    (CarrierCharge.step_bound_charged (keyAt walk) (AnswerCarrier.carrierRightKeep walk)
      walk.1.1.2.1 (keyAt walk))
    ServedAgreement.startServingOn ServedAgreement.stopServingOn
    bracket_startServingOn bracket_stopServingOn
    (fun keys : SecretKey × PublicKey =>
      recordedAdversaryImpl + recordedSigningOracle (Scheme.sign keys.1))
    (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2)
    (fun keys : SecretKey × PublicKey => adversary.main keys.2)
    (fun (keys : SecretKey × PublicKey) (forgery : Forgery) =>
      countRecorded verifierCost (Scheme.verify keys.2 forgery.message forgery.signature))
    (fun (_ : SecretKey × PublicKey) (forgery : Forgery) (tally : Multiplicative Tally)
        (log : SigningLog) (verified : Bool × Tally) (state : CountedState) =>
      ((({ forgery := forgery
           signed := log
           verified := verified.1
           counts := (Multiplicative.toAdd tally).1 + verified.2.1 },
        (Multiplicative.toAdd tally).2 + verified.2.2), state.2.2), forgetCarrier state))
    (fun result => LateProbes.Ordering (walk, result))
    (fun result => Multiset.card (LateProbes.probes (walk, result)))
    (fun _ _ _ _ _ _ hfired => hfired)
    (fun _ _ _ _ _ _ => by
      rw [LateProbes.card_probes_of_good hgood]
      exact le_rfl)
    (startAt walk.2, (([], []), 0))
    (by
      rintro ⟨entry, hentryMem, -⟩
      rw [forgetCarrier] at hentryMem
      exact absurd hentryMem (by simp))
  rw [carrierTail, handlerAt]
  refine le_trans hmain ?_
  have hpot : CarrierCharge.potentialAt (LateCharge.Spent walk.1.1.2.1 (keyAt walk))
      (startAt walk.2, (([], []), (0 : Nat))) = 0 := rfl
  have hgauge : CarrierCharge.gaugeAt (startAt walk.2, (([], []), (0 : Nat))) = 0 := rfl
  rw [hpot, Nat.cast_zero, zero_mul, zero_add, hgauge,
    show (fun w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState =>
        Multiset.card (LateProbes.probes (walk, w)) - 0) =
      (fun w : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState =>
        Multiset.card (LateProbes.probes (walk, w))) from funext fun w => Nat.sub_zero _,
    LateRate.rate, mul_one_div]

/-! ## And the socket's hypothesis

`BracketedOrdering.prob_ordering_le` wanted two things: the containment, which
`probes_le_recordMessageClass_carrierTail` gives at any test implying the carrier's, and the
per-walk charge, which is the theorem above. This is the two of them, and it is `hordering` in
the shape `ObligationShapes.sharedChargedLate_of_parts_at` names.

`LateProbes.ForgetsTo` — that forgetting the carrier tail's recordings returns the recorded
paired run — is the presentation equation rather than a charge, and `CarrierTail.forgetsTo`
already proves it for an arbitrary `rightKeep`, so it holds at `chargedKeepAt` with nothing
written. The hypothesis-free form below is therefore the end of this half: `hordering` as
`ObligationShapes.sharedChargedLate_of_parts_at` names it, with no input left to supply. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering term at the carrier tail.** -/
theorem prob_ordering_le_carrierTail (adversary : Adversary)
    (hforget : LateProbes.ForgetsTo (carrierTail chargedKeepAt) adversary) :
    Pr[fun pair : LateProbes.SplitPair =>
        Target.GoodWalk pair.1 ∧ LateProbes.Ordering pair |
        LateProbes.pairedOf (carrierTail chargedKeepAt) adversary] ≤
      expected (LateProbes.pairedOf (carrierTail chargedKeepAt) adversary)
          (fun pair => Multiset.card (SharedJoin.recordMessageClass
            (LateProbes.forgetRecordings pair))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  BracketedOrdering.prob_ordering_le
    (fun walk _ hgood => prob_ordering_perWalk adversary walk hgood)
    (BracketedOrdering.probes_le_recordMessageClass_carrierTail chargedKeepAt
      chargedKeepAt_carrierRightKeep adversary hforget)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering term at the carrier tail, with nothing assumed.** `CarrierTail.forgetsTo` is
stated for an arbitrary test, so it holds at `chargedKeepAt` directly. -/
theorem prob_ordering_le_carrierTail' (adversary : Adversary) :
    Pr[fun pair : LateProbes.SplitPair =>
        Target.GoodWalk pair.1 ∧ LateProbes.Ordering pair |
        LateProbes.pairedOf (carrierTail chargedKeepAt) adversary] ≤
      expected (LateProbes.pairedOf (carrierTail chargedKeepAt) adversary)
          (fun pair => Multiset.card (SharedJoin.recordMessageClass
            (LateProbes.forgetRecordings pair))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  prob_ordering_le_carrierTail adversary (forgetsTo chargedKeepAt adversary)

end SlhDsaSecurity.CarrierOrdering

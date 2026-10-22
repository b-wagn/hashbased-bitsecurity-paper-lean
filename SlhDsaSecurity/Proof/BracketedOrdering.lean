import SlhDsaSecurity.Proof.CarrierRecord
import SlhDsaSecurity.Proof.LateProbes

/-!
# The ordering defect's two lemmas, for a tail that is not a recorder run

`ObligationShapes.sharedChargedLate_of_parts_at` asks for one thing about the ordering defect:
the charge read against the join's message-class part. `LateProbes` reaches it in two steps —
a containment putting the recorder's probes inside that part, and the charge read at the probe
count — and both of its versions go through `LateProbes.IsRecorderRun`, which a **bracketed**
tail fails by construction: a bracketed run is three runs with a framing raised and lowered
between them, not one `simulateQ` of one computation.

So the two steps are restated here with the recorder run replaced by exactly what each of them
used it for, and nothing else.

**The containment used it for two facts about the recording**, which it obtained from
`SplitPrefix.right_record_nodup` and `LateProbes.messageClass_of_record`. Here they are
hypotheses, stated at the pair rather than at a run, because that is the form a bracketed tail
can supply: `CarrierTailRecordings` carries both invariants across the three stages, and the
invariant is a statement about the state the tail ends at, not about any one run inside it.

**The charge used it for the per-walk bound**, which is the one thing a bracketed tail still owes
and the one thing this file does not prove. It is a hypothesis, in the same position `hrecord`
holds in the containment, so that the socket can be filled the moment the bound exists and no
part of the assembly has to be revisited then.

Both lemmas are stated for an arbitrary `LateProbes.FusedTail`. The instantiation at the carrier
tail follows, for the containment, which is the half whose inputs exist.

The carrier instantiation is stated at **any** test implying
`AnswerCarrier.carrierRightKeep`, because the charge one layer down needs a strictly stronger
one: `CarrierCharge.chargedRightKeep` adds the exclusion the step bound asks for. A stronger test
only shrinks the recording, so both recording invariants and `hrecord` hold at it with the
implication threaded through and nothing reproved.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BracketedOrdering

open Security ClassExpectation

variable {fused : LateProbes.FusedTail} {adversary : Adversary}

/-! ## The containment -/

/-- **The probes sit inside the join's message-class part**, for any tail whose target recording
holds each input once and holds only message-class inputs.

`hrecord` is the provenance step, exactly as in `LateProbes.probes_le_recordMessageClass`; the
two recording hypotheses are what that version read off the recorder run. -/
theorem probes_le_recordMessageClass
    (hforget : LateProbes.ForgetsTo fused adversary)
    (hnodup : ∀ pair ∈ support (LateProbes.pairedOf fused adversary),
      (pair.2.2.2.2.map Prod.fst).Nodup)
    (hclass : ∀ pair ∈ support (LateProbes.pairedOf fused adversary),
      ∀ entry ∈ pair.2.2.2.2,
        CombinedCharge.IsMessageInput (LateProbes.keyOfPair pair) entry.1)
    (hrecord : ∀ pair ∈ support (LateProbes.pairedOf fused adversary),
      Target.GoodWalk pair.1 → ∀ entry ∈ pair.2.2.2.2,
        entry.1 ∈ SharedJoin.recordOf (LateProbes.forgetRecordings pair)) :
    ∀ pair ∈ support (LateProbes.pairedOf fused adversary),
      LateProbes.probes pair ≤
        SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair) := by
  classical
  intro pair hpair
  by_cases hgood : Target.GoodWalk pair.1
  · rw [LateProbes.probes, if_pos hgood]
    exact LateProbes.probesOf_le_recordMessageClass adversary
      (LateProbes.mem_support_forget hforget hpair) hgood pair.2.2.2.2 (hnodup pair hpair)
      (hclass pair hpair) (hrecord pair hpair hgood)
  · exact LateProbes.probes_le_of_not_good hgood _

/-! ## The charge

The per-walk bound is the hypothesis, **and it carries `Target.GoodWalk`.** That is not a
convenience: off a good walk `LateProbes.probes` is empty, so the hypothesis without the guard
would read `Pr[Ordering] ≤ 0` and be false. The event being charged carries `GoodWalk` too, so
the walk-wise charge is discharged outright on a bad walk and the hypothesis is only read where
it has content.

The guard was missing when this lemma was first written and the error was invisible until its
consumer: at the one layer where the bound is read, `GoodWalk` is in hand, so nothing complained
until a proof had to produce the hypothesis for every walk. Same family as the dropped
witnesses — a statement the proof could not have supported, found by the consumer rather than by
the proof. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The ordering term, at the pair that carries the recordings**, from the per-walk charge
rather than from a recorder run. -/
theorem prob_ordering_le
    (hcharge : ∀ walk ∈ support WarmedGame.graphWalk, Target.GoodWalk walk →
      Pr[fun result => LateProbes.Ordering (walk, result) | fused adversary walk] ≤
        expected (fused adversary walk)
            (fun result => Multiset.card (LateProbes.probes (walk, result))) /
          ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hprobes : ∀ pair ∈ support (LateProbes.pairedOf fused adversary),
      LateProbes.probes pair ≤
        SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair)) :
    Pr[fun pair : LateProbes.SplitPair =>
        Target.GoodWalk pair.1 ∧ LateProbes.Ordering pair |
        LateProbes.pairedOf fused adversary] ≤
      expected (LateProbes.pairedOf fused adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (LateProbes.prob_le_expected_of_perWalk fused adversary
    (fun pair => Target.GoodWalk pair.1 ∧ LateProbes.Ordering pair)
    (fun pair => Multiset.card (LateProbes.probes pair)) 0 fun walk hwalk => ?_) ?_
  · rw [add_zero]
    by_cases hgood : Target.GoodWalk walk
    · exact le_trans (probEvent_mono fun result _ hbad => hbad.2) (hcharge walk hwalk hgood)
    · rw [probEvent_eq_zero fun result _ hbad => hgood hbad.1]
      exact zero_le
  · rw [add_zero]
    exact ENNReal.div_le_div_right (expected_mono _ _ _
      fun pair hpair => Multiset.card_le_card (hprobes pair hpair)) _

/-! ## The containment at the carrier tail

Both recording hypotheses are the invariants `CarrierTailRecordings` carries across the three
stages, and the provenance step is `CarrierRecord.hrecord`. Nothing here is a port: the two
invariants were stated at the tail's own final state, which is the object the hypotheses name. -/

set_option maxHeartbeats 1000000 in
/-- **The carrier tail's probes sit inside the join's message-class part.** -/
theorem probes_le_recordMessageClass_carrierTail
    (rightKeep : BracketedRun.Walk → Bytes → HandlerCarrier.State → Prop)
    (hright : ∀ (walk : BracketedRun.Walk) (input : Bytes) (view : HandlerCarrier.State),
      rightKeep walk input view → AnswerCarrier.carrierRightKeep walk input view)
    (adversary : Adversary)
    (hforget : LateProbes.ForgetsTo (CarrierTail.carrierTail rightKeep) adversary) :
    ∀ pair ∈ support (LateProbes.pairedOf (CarrierTail.carrierTail rightKeep) adversary),
      LateProbes.probes pair ≤
        SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair) := by
  classical
  refine probes_le_recordMessageClass hforget ?_ ?_
    (CarrierRecord.hrecord rightKeep hright adversary)
  · intro pair hpair
    obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := LateProbes.mem_support_pairedOf hpair
    subst hvalue
    exact (CarrierTailRecordings.recordFreshNodup_carrierTail rightKeep
      adversary walk result hresult).2
  · intro pair hpair entry hentry
    obtain ⟨walk, hwalk, result, hresult, hvalue⟩ := LateProbes.mem_support_pairedOf hpair
    subst hvalue
    exact CarrierTailRecordings.recordClass_carrierTail rightKeep
      (fun walk input => CombinedCharge.IsMessageInput (CarrierTail.keyAt walk) input)
      (fun walk input view hkeep =>
        AnswerCarrier.carrierRightKeep_class walk input view (hright walk input view hkeep))
      adversary walk result hresult entry hentry

end SlhDsaSecurity.BracketedOrdering

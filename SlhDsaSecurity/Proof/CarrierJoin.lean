import SlhDsaSecurity.Proof.CarrierCover
import SlhDsaSecurity.Proof.CoverageRouted
import SlhDsaSecurity.Proof.BlockViews

/-!
# From the forgery's coverage event to the target recording's

The cache side's assembly, redone at the carrier. `CoverageRouted.ForgeryDisclosedCovered` says
the forgery's own digest is covered — it is cached, it does not disclose, and for each of the
fourteen FORS trees some *disclosing* cached input supplies the same leaf.
`BlockViews.TargetCovered` says the same thing in the coordinates the charge is read at: some
entry of the **target** recording has all fourteen leaves supplied by entries of the
**disclosing** recording.

Going from the first to the second is one argument and it is the same one
`SplitWitness.Served.mem_records_of_covered_narrow` makes: put each of the inputs the coverage
event names into a recording, using the cover, and then read off which recording each landed in.

**What the cover gives and what decides the side.** `CarrierCover.cover_carrierTail` says a query
the run ends holding is recorded on one side or the other. It does not say which. The side is
decided by the disclosing class and by nothing else:

* the forgery's own digest is **not** disclosing — that is `ForgeryCoveredBy`'s own clause — so it
  cannot be in the disclosing recording, and the cover puts it in the target one;
* each witness **is** disclosing, so it cannot be in the target recording, and the cover puts it
  in the disclosing one.

So the argument needs exactly two facts about the recordings, and they are stated as hypotheses
here rather than assumed silently: every disclosing-recorded input is in the class, and no
target-recorded input is.  It needs one more about the class itself — that a disclosing input is
one the cover applies to — which is `SplitWitness.disclosingKeep_class`'s job on the cache route
and is the only place the witnesses' class enters. The first is the carrier's `CarriedWitness.mem_served_of_mem_leftRecord`
read through the served/log agreement; the second is `¬LateDisclosure` read through
`ServedRandomised.signerRandomised_of_served`. Both are transports along the tail and both belong
to the threads carrying them there; neither is part of this argument.

**The class is a parameter.** Nothing below reads what `disclosing` is, which is why the same
proof serves the served-log class and any class the two recordings are split by. That also means
there is no frame-conditional anywhere in here: the carrier's residue lives in the *class* the
cover is taken at, exactly where the cache route put it, and this file never looks at it.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarrierJoin

open Security BracketedRun CarrierTail CoverageRouted

/-- **The forgery's coverage event, read in the recordings.**

Four hypotheses and no arithmetic: the cover, the two class facts about the recordings, and
freshness of the inputs the coverage event names. -/
theorem targetCovered_of_forgeryCoveredBy
    (disclosing : Bytes → Prop) (pk : PublicKey) (inClass : Bytes → Prop)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (value : Outcome × Nat)
    (hvalue : value.1 = result.1.1.1)
    (hcover : ∀ (input : Bytes) (answer : HashOutput), inClass input →
      result.2.1 input = some answer →
        (input, answer) ∈ result.2.2.1 ∨ (input, answer) ∈ result.2.2.2)
    (hleftClass : ∀ entry ∈ result.2.2.1, disclosing entry.1)
    (hrightClass : ∀ entry ∈ result.2.2.2, ¬ disclosing entry.1)
    (hclass : ∀ input : Bytes, CombinedCharge.IsMessageInput pk input → inClass input)
    (hdisclosingClass : ∀ input : Bytes, disclosing input → inClass input)
    (hcovered : ForgeryCoveredBy disclosing pk (value, result.2.1)) :
    BlockViews.TargetCovered (σ := QueryCache HashSpec) result := by
  classical
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hnotself, hcoveredAt⟩ := hcovered
  -- The forgery's own digest is in the target recording, because it does not disclose.
  have htarget : (Hashing.messageInput parsed.randomizer pk message, answer) ∈ result.2.2.2 := by
    rcases hcover (Hashing.messageInput parsed.randomizer pk message) answer
      (hclass _ ⟨parsed.randomizer, message, rfl⟩) hentry with hleft | hright
    · exact absurd (hleftClass _ hleft) hnotself
    · exact hright
  refine ⟨(Hashing.messageInput parsed.randomizer pk message, answer), htarget, fun tree => ?_⟩
  -- And each witness is in the disclosing recording, because it does.
  obtain ⟨other, otherAnswer, hne, hdisclosing, hother, hinstance, hleaf⟩ := hcoveredAt tree
  rcases hcover other otherAnswer (hdisclosingClass other hdisclosing) hother with
    hleft | hright
  · exact ⟨(other, otherAnswer), hleft, hinstance, hleaf⟩
  · exact absurd hdisclosing (hrightClass _ hright)

/-! ## The same, at the carrier tail

`CarrierCover.cover_carrierTail` discharges the cover, so what is left at the tail is the two
class facts about the recordings and freshness at the walk's own cache. -/

set_option maxHeartbeats 1000000 in
/-- **The forgery's coverage event, read in the carrier tail's recordings.** -/
theorem targetCovered_carrierTail
    (rightKeep : Walk → Bytes → HandlerCarrier.State → Prop)
    (inClass : Bytes → Prop) (disclosing : Bytes → Prop)
    (adversary : Adversary) (walk : Walk)
    (hcoverTests : ∀ (probe : Bytes) (view : HandlerCarrier.State), inClass probe →
      @RecorderView.CacheView.cacheOf HandlerCarrier.State
          (CarriedWitness.servingView (keyAt walk)) view probe = none →
        CarriedWitness.disclosingKeep (keyAt walk) probe view ∨ rightKeep walk probe view)
    (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState)
    (hresult : result ∈ support (carrierTail rightKeep adversary walk))
    (hfreshWalk : ∀ input : Bytes, inClass input → walk.2 input = none)
    (hleftClass : ∀ entry ∈ result.2.2.1, disclosing entry.1)
    (hrightClass : ∀ entry ∈ result.2.2.2, ¬ disclosing entry.1)
    (hclass : ∀ input : Bytes, CombinedCharge.IsMessageInput (keyAt walk) input → inClass input)
    (hdisclosingClass : ∀ input : Bytes, disclosing input → inClass input)
    (value : Outcome × Nat) (hvalue : value.1 = result.1.1.1)
    (hcovered : ForgeryCoveredBy disclosing (keyAt walk) (value, result.2.1)) :
    BlockViews.TargetCovered (σ := QueryCache HashSpec) result :=
  targetCovered_of_forgeryCoveredBy disclosing (keyAt walk) inClass result value hvalue
    (fun input answer hin hfinal =>
      CarrierCover.cover_carrierTail rightKeep inClass adversary walk hcoverTests result hresult
        input answer hin (hfreshWalk input hin) hfinal)
    hleftClass hrightClass hclass hdisclosingClass hcovered

end SlhDsaSecurity.CarrierJoin

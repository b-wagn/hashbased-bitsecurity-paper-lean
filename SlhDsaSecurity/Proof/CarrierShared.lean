import SlhDsaSecurity.Proof.CarrierOrdering
import SlhDsaSecurity.Proof.ObligationShapes

/-!
# The shared half, at the carrier tail

`ObligationShapes.sharedChargedLate_of_parts_at` takes four parts. Three are in hand at this
tail: the forgetting equation is `CarrierTail.forgetsTo`, the ordering term is
`CarrierOrdering.prob_ordering_le_carrierTail'`, and the seed term is below. The fourth,
`hinput`, is the input half's bullet and belongs to the thread that owns it; it is this file's
one named import and nothing here depends on how it is discharged.

**On the seed term, and a correction to what I previously reported.** `sharedChargedLate_at`
below is parametric in `seedEvent` and `seedUnits`, and `sharedChargedLate_clear` is the
`seedUnits := 0` instance. The second is a true theorem — with `seedEvent := fun _ => False` the
charge is `0 ≤ 0` — but it is **only useful if the answer half can also be taken at
`late := LateProbes.Ordering`**, since `Obligations.target_of_charges_fused_at` reads one `late`
on both sides. And that does **not** follow from `CarrierClearFraming.clear_stages`.

Here is why, because the gap is exact. `SplitWitness.Served.mem_recordOf_of_cache_reaches`
consults its cover once, at the view the forgery's digest input is *answered* at, and threads
`reaches` to get there — so `reaches` has to be an invariant of the whole run, not a fact about
its start. `clear_stages` gives the three stage **starts**. The middle stage's brackets raise the
framing, so `reaches := fun state => state.framing = none` is not carried through a signing
sub-run; and that is the very fact `RecordInvariant.phase_invariant_of_after` was written for —
*a framing invariant is broken by the opening bracket on purpose.* I had read `clear_stages` as
discharging the demand and it does not: it discharges it at the stage starts and at the
adversary's own steps, which is where the framing is clear, and says nothing about the views
inside a sub-run.

What the sub-runs actually need, for whoever takes the answer half: a sub-run serving frame `f`
answers only its own two inputs (`SignerRandomiser.probes_signInternalAt`, already proved and
already used by `CarrierRecord.hrecord`). So if the forgery's digest input is answered inside
one, either `f` is the forgery's own frame — and then `HandlerCarrier.FilesLeft` holds and the
cover's **left** disjunct closes it, with the demand never consulted — or the forgery's digest
input coincides with `Hashing.randomizerInput` at `f`, which by
`Hashing.randomizerInput_injective` forces the published randomiser to be `SK.prf`. That is
`AnswerCoverage.ForgerySeedRandomised`: the leftover, unreduced.

So on this route the leftover is needed in **one** place rather than at every view — a sub-run
serving a frame other than the forgery's — but it is still needed, and `seedUnits := 0` is not
earned by the stage starts alone. Both forms are provided so that the shared half is ready
whichever way the answer half goes.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierShared

open Security WarmedGame Target CarrierTail CarrierOrdering

/-- **The seed event is empty on this route**, so its charge is zero units and not a bound. -/
theorem prob_seed_le (adversary : Adversary) :
    Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ (False : Prop) |
        LateProbes.pairedOf (carrierTail chargedKeepAt) adversary] ≤
      ((0 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [probEvent_eq_zero fun pair _ hbad => hbad.2]
  exact zero_le

set_option maxHeartbeats 1000000 in
/-- **The shared half at the carrier tail**, parametric in what the answer half cannot rule out.
`hordering` and `hforget` are discharged here; `hinput` and `hseed` are the two imports, and
`late` is whatever the two sides agree on. -/
theorem sharedChargedLate_at (claims seedUnits : Nat)
    (late seedEvent : LateProbes.SplitPair → Prop) (hclaims : 259 + seedUnits ≤ claims)
    (hlate : ∀ pair : LateProbes.SplitPair, late pair →
      LateProbes.Ordering pair ∨ seedEvent pair)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBulletAt (carrierTail chargedKeepAt) adversary LateProbes.Ordering)
    (hseed : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : LateProbes.SplitPair => GoodWalk pair.1 ∧ seedEvent pair |
        LateProbes.pairedOf (carrierTail chargedKeepAt) adversary] ≤
        ((seedUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Obligations.SharedChargedLate claims (carrierTail chargedKeepAt)
      FinalAssembly.forgetFused late :=
  ObligationShapes.sharedChargedLate_of_parts_at (carrierTail chargedKeepAt) claims seedUnits
    late seedEvent hclaims hlate
    (fun adversary => forgetsTo chargedKeepAt adversary)
    (fun adversary => prob_ordering_le_carrierTail' adversary)
    hinput hseed

set_option maxHeartbeats 1000000 in
/-- **And at no seed charge at all**, which is the form to use *if* the answer half can be taken
at `LateProbes.Ordering`. The header says what that still needs; this theorem does not establish
it and does not depend on it. -/
theorem sharedChargedLate_clear (claims : Nat) (hclaims : 259 ≤ claims)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBulletAt (carrierTail chargedKeepAt) adversary LateProbes.Ordering) :
    Obligations.SharedChargedLate claims (carrierTail chargedKeepAt)
      FinalAssembly.forgetFused LateProbes.Ordering :=
  sharedChargedLate_at claims 0 LateProbes.Ordering (fun _ => False) (by omega)
    (fun _ hlate => Or.inl hlate) hinput (fun _ adversary _ => prob_seed_le adversary)

end SlhDsaSecurity.CarrierShared

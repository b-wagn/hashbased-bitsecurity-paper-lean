import SlhDsaSecurity.Proof.InputBullet
import SlhDsaSecurity.Proof.CarrierTail
import SlhDsaSecurity.Proof.Target
import SlhDsaSecurity.Proof.Obligations

/-!
# The `127` socket with the ordering charge gone and the seed charge kept

`Target.target_of_obligations_fused_at` takes a `late` event that the answer half may rule out
and the shared half pays for. Every earlier instantiation took `late` to contain the **ordering
defect** — a target-recorded digest that a later signature serves — and paid for it at the
record's message-class part. That is one unit of `2 ^ -128` per message-class query, and the same
query is also a guess at `SK.prf` (its randomiser field) and a coverage target. Three units per
query against a target of two is why every ledger built on it stopped at `126`.

**The seed guess cannot be the charge that goes.** With `SK.prf` in hand an adversary computes the
digest of any message before asking for its signature, and so chooses which signatures to request
by where their FORS leaves land: covering one target's fourteen leaves at its own instance takes
about `2 ^ 78` queries, after which the forgery is certain. So a query spent finding `SK.prf` buys
a forgery, at one stake per query, and the charge on the record's `PRF_msg` candidates is real.

**The ordering defect can go.** A pre-queried digest that a later signature serves is one whose
randomiser the adversary guessed before the `PRF_msg` answer existed; that answer is a fresh draw,
so the event is thinned by `2 ^ -128` *on top of* whatever coverage it helps, and its total effect
is second order. The answer half absorbs it inside its own column — that is the answer side's
obligation below, stated with nothing excluded but the seed guess.

So this socket takes `late := PrfHit`: some query the adversary or the verifier made is a
`PRF_msg` input at the walk's `SK.prf`. The shared half pays for it at the record entries **not**
prefixed by `PK.seed` — the only ones that can carry `SK.prf` on a good walk — which are disjoint
from the aiming part the input half pays at, so the two fit in one record:
`aiming + candidates ≤ record ≤ q - 2 ^ subtreeHeight`.

What is assumed here, stated in the shape each producer will deliver:

* `hanswer` — the answer half at the carrier tail, with only `PrfHit` excluded;
* `hclaims` — `InputBullet.ClaimsCharged`, the input half;
* `hprf` — the seed guess, at the record's candidate part (the game hop's output).
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Target127

open Security WarmedGame Target ClassExpectation SharedJoin RandomiserRecord LateProbes

/-! ## The seed guess and the record part that pays for it -/

/-- An input whose first `n` bytes are the encoding of `seed`. -/
def SeedPrefixed (seed : Digest) (input : Bytes) : Prop :=
  ∃ rest : Bytes, input = bytesBE n seed ++ rest

/-- **The seed guess.** Some query of the adversary or the verifier is a `PRF_msg` input at the
walk's `SK.prf`. -/
def PrfHit (pair : RecordedPair) : Prop :=
  RecordMeetsPrfClass pair.1.1.1.2.1 pair.2

/-- **The defect at the split pair**: the seed guess, read through the recordings' forgetting. -/
def late (pair : SplitPair) : Prop := PrfHit (forgetRecordings pair)

open scoped Classical in
/-- **The record's `PRF_msg` candidates**: its entries not prefixed by `PK.seed`. -/
noncomputable def recordPrfCandidates (pair : RecordedPair) : Multiset Bytes :=
  (recordOf pair).filter fun input => ¬ SeedPrefixed pair.1.1.1.2.2 input

/-- A `PRF_msg` input at `prf` is prefixed by `prf`. -/
theorem seedPrefixed_of_prfClass {prf : Digest} {input : Bytes}
    (hprf : RandomizerGate.PrfClass prf input) : SeedPrefixed prf input := by
  obtain ⟨seed, message, rfl⟩ := hprf
  exact ⟨bytesBE n seed ++ message, by simp [Hashing.randomizerInput, List.append_assoc]⟩

/-- Two seeds' prefixes are the same prefix only when the seeds are equal. -/
theorem eq_of_seedPrefixed {left right : Digest} {input : Bytes}
    (hleft : SeedPrefixed left input) (hright : SeedPrefixed right input) : left = right := by
  obtain ⟨leftRest, rfl⟩ := hleft
  obtain ⟨rightRest, hsame⟩ := hright
  have htake := congrArg (List.take n) hsame
  simp only [List.take_left' (length_bytesBE n left), List.take_left' (length_bytesBE n right)]
    at htake
  exact bytesBE_injective n htake

/-- **An aiming probe is prefixed by `PK.seed`**: it is a tweakable input at the public seed. -/
theorem seedPrefixed_of_aimsSomewhere {publicSeed : Digest} {input : Bytes}
    (haims : RedrawCell.AimsSomewhere publicSeed input) : SeedPrefixed publicSeed input := by
  classical
  rw [RedrawCell.AimsSomewhere, GraphStakes.locate] at haims
  split at haims
  · rename_i hsome
    obtain ⟨node, cell, rfl⟩ := hsome
    exact ⟨node.parent.address.toBytes ++ bytesBE n cell,
      by simp [GraphStakes.inputOf, Hashing.tweakableInput, List.append_assoc]⟩
  · exact absurd rfl haims

open scoped Classical in
/-- **The two shared parts fit in one record.** Aiming probes are `PK.seed`-prefixed and the
candidates are not, so they are disjoint filters of the record. -/
theorem card_aiming_add_candidates_le_record (pair : RecordedPair) :
    Multiset.card (recordAiming pair) + Multiset.card (recordPrfCandidates pair) ≤
      Multiset.card (recordOf pair) := by
  classical
  have haim : recordAiming pair ≤
      (recordOf pair).filter fun input => SeedPrefixed pair.1.1.1.2.2 input := by
    rw [recordAiming]
    exact Multiset.monotone_filter_right _ fun input haims =>
      seedPrefixed_of_aimsSomewhere haims
  have hsplit := Multiset.filter_add_not (fun input => SeedPrefixed pair.1.1.1.2.2 input)
    (recordOf pair)
  calc Multiset.card (recordAiming pair) + Multiset.card (recordPrfCandidates pair)
      ≤ Multiset.card ((recordOf pair).filter fun input => SeedPrefixed pair.1.1.1.2.2 input) +
          Multiset.card (recordPrfCandidates pair) :=
        Nat.add_le_add_right (Multiset.card_le_card haim) _
    _ = Multiset.card (recordOf pair) := by
        rw [recordPrfCandidates, ← Multiset.card_add, hsplit]

/-- **On a good walk a seed guess is a candidate.** The walk's `SK.prf` differs from its
`PK.seed`, so an input carrying the first is not prefixed by the second. -/
theorem exists_candidate_of_prfHit (pair : RecordedPair) (hgood : GoodWalk pair.1)
    (hhit : PrfHit pair) :
    ∃ input ∈ recordPrfCandidates pair, RandomizerGate.PrfClass pair.1.1.1.2.1 input := by
  classical
  obtain ⟨input, hinput, hprf⟩ := hhit
  refine ⟨input, ?_, hprf⟩
  rw [recordPrfCandidates, Multiset.mem_filter]
  refine ⟨Multiset.mem_toFinset.mp hinput, fun hseed => hgood.1 ?_⟩
  exact eq_of_seedPrefixed (seedPrefixed_of_prfClass hprf) hseed

/-! ## The shared half, from the input half and the seed charge -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The shared half at any tail that forgets to the recorded one**, from the input half's
obligation and the seed charge at the candidates, inside one record's worth of the budget. -/
theorem shared_of_parts (fused : FusedTail) (q : Nat) (adversary : Adversary)
    (hforget : ForgetsTo fused adversary) (hbudget : HasTotalBudget adversary q)
    (hclaims : InputBullet.ClaimsCharged adversary)
    (hprf : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ PrfHit pair |
        recordedPairedRun adversary] ≤
      expected (recordedPairedRun adversary)
          (fun pair => Multiset.card (recordPrfCandidates pair)) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[fun pair => GoodWalk pair.1 ∧
        (RoutedSplit.InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ late pair) |
      pairedFused (fused adversary)] ≤
      ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hpaired : pairedFused (fused adversary) = pairedOf fused adversary := rfl
  rw [hpaired]
  have hmove : Pr[fun pair => GoodWalk pair.1 ∧
        (RoutedSplit.InputBad ((pair.1.1, (FinalAssembly.forgetFused pair.2).1),
          (FinalAssembly.forgetFused pair.2).2) ∨ late pair) | pairedOf fused adversary] =
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
          (RoutedSplit.InputBad (recordedTraceOf pair) ∨ PrfHit pair) |
        recordedPairedRun adversary] :=
    probEvent_forget hforget
      (fun pair : RecordedPair => GoodWalk pair.1 ∧
        (RoutedSplit.InputBad (recordedTraceOf pair) ∨ PrfHit pair))
  rw [hmove]
  have hparts : expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordAiming pair)) +
      expected (recordedPairedRun adversary)
        (fun pair => Multiset.card (recordPrfCandidates pair)) ≤
      ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    rw [← expected_add]
    exact expected_le_of_le _ _ _ fun pair hpair =>
      le_trans (card_aiming_add_candidates_le_record pair)
        (card_record_le_budget adversary q hbudget hpair)
  calc Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
          (RoutedSplit.InputBad (recordedTraceOf pair) ∨ PrfHit pair) |
        recordedPairedRun adversary]
      ≤ Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧
            RoutedSplit.InputBad (recordedTraceOf pair) | recordedPairedRun adversary] +
          Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ PrfHit pair |
            recordedPairedRun adversary] := by
        refine le_trans (probEvent_mono (q := fun pair : RecordedPair =>
          (GoodWalk pair.1 ∧ RoutedSplit.InputBad (recordedTraceOf pair)) ∨
            (GoodWalk pair.1 ∧ PrfHit pair)) fun pair _ hpair =>
          hpair.2.imp (fun h => ⟨hpair.1, h⟩) fun h => ⟨hpair.1, h⟩) ?_
        exact probEvent_or_le _ _ _
    _ ≤ (expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordAiming pair)) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordPrfCandidates pair)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := add_le_add hclaims hprf
    _ = (expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordAiming pair)) +
          expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordPrfCandidates pair)) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same]
        ring_nf
    _ ≤ (((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        by gcongr
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        (congrArg (fun total : ℝ≥0∞ => total / ((2 ^ 128 : Nat) : ℝ≥0∞))
          (Nat.cast_add (q - 2 ^ subtreeHeight) 259)).symm

/-! ## The target -/

set_option maxHeartbeats 1000000 in
/-- **`127`, from three obligations.** The answer half at the carrier tail with the seed guess
excluded and nothing else; the input half; and the seed guess charged at the record's
`PRF_msg` candidates. The walk's two coincidences, the answer half's constant and the forgery's
`259` claims share the `2 ^ subtreeHeight` cells key generation pays for. -/
theorem target_of_parts (answerDefect : ℝ≥0∞) (defectUnits : Nat)
    (hdefect : defectsAt answerDefect ≤
      ((defectUnits : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hfits : 259 + defectUnits ≤ 2 ^ subtreeHeight)
    (keep : BracketedRun.Walk → Bytes → HandlerCarrier.State → Prop)
    (hanswer : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result => RoutedSplit.AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1),
              (FinalAssembly.forgetFused result).2) ∧ ¬ late (walk, result) |
            CarrierTail.carrierTail keep adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + answerDefect)
    (hclaims : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      InputBullet.ClaimsCharged adversary)
    (hprf : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ PrfHit pair |
          recordedPairedRun adversary] ≤
        expected (recordedPairedRun adversary)
            (fun pair => Multiset.card (recordPrfCandidates pair)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    HasTotalSecurityBits .strong 127 :=
  Obligations.target_of_charges_fused_at answerDefect 259 defectUnits hdefect hfits
    (CarrierTail.carrierTail keep) FinalAssembly.forgetFused late
    (fun adversary walk => CarrierTail.forgetFused_carrierTail keep adversary walk)
    hanswer
    (fun q adversary _ hbudget => shared_of_parts (CarrierTail.carrierTail keep) q adversary
      (CarrierTail.forgetsTo keep adversary) hbudget (hclaims q adversary hbudget)
      (hprf q adversary hbudget))

end SlhDsaSecurity.Target127

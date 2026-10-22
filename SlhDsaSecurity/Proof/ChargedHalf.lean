import SlhDsaSecurity.Proof.ServingTable
import SlhDsaSecurity.Proof.CarrierAvailability

/-!
# The charge, composed at the half's own run

Everything the charge asks for is now in hand, and this file hands it over. What is charged is
`TouchedKeys.honestLinked` — the honest game at a drawn table, keys handed in, one computation —
answered by the handler that files, at the availability the carrier's served set determines.

**The one thing the chain did not already supply is the seed, and how it is supplied matters.**
The charge reads its reveal count off the run's value, by `revealedOf`, because the event is
evaluated outside the table draw. `honestLinked`'s value does not carry the drawn seed, so the
computation is wrapped. The obvious wrapper carries the reveal *function* — and it is wrong:
`hreadsRevealed` becomes immediate, but `hrevealedOf` is **unconditional**, the carried component
is an arbitrary function of its type off the support, and nothing bounds it there.

`seededLinked` carries the **seed cell** instead. Then `hrevealedOf` is
`GraphStakes.honestRevealed_le` at the carried seed, which holds at *every* seed and so holds
unconditionally, and `hreadsRevealed` is `support_map`. The rule the two wrappers teach is worth
more than either: **carry the thing the unconditional hypothesis is about, not the thing the
conditional one is about.** A wrapper that makes a support-conditioned hypothesis trivial can
make an unconditional one unprovable, and which way round it goes is not visible until both are
written.

The wrapper inherits its own blindness: two tables agreeing on `RedrawCell.seedAndRoot` agree at
the secret seed, so they carry the same seed, and `TouchedKeys.touched_honestLinked` does the
rest. That is the same pair of cells paying for a fourth thing.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ChargedHalf

open Security CanonicalGraph OpenCache ServingProgram HandlerFacts
open WalkTable TableTail ServingTable

/-! ## The run, carrying the seed it was drawn at -/

/-- The honest linked run's value, with the drawn table's secret seed beside it. -/
abbrev SeededValue : Type :=
  ((((Forgery × Multiplicative RecordedQueries.Tally) ×
    (Bool × RecordedQueries.Tally)) × SigningLog)) × Digest

/-- **The honest linked run, carrying the seed cell of the table it was run at.** -/
noncomputable def seededLinked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : OracleComp OracleWorld SeededValue :=
  (fun value => (value, table.1 Node.secretSeed)) <$>
    TouchedKeys.honestLinked adversary prfSeed publicSeed table

/-- **The carried seed is the table's.** -/
theorem seed_of_mem_support (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding) (value : SeededValue)
    (hvalue : value ∈ support (seededLinked adversary prfSeed publicSeed table)) :
    value.2 = table.1 Node.secretSeed := by
  rw [seededLinked, support_map] at hvalue
  obtain ⟨inner, -, hpair⟩ := hvalue
  rw [← hpair]

/-- **The wrapper is blind off the seed and the root too.** The run was, by
`TouchedKeys.touched_honestLinked`; what is carried beside it is the seed cell, and two tables
agreeing on `RedrawCell.seedAndRoot` agree at that. -/
theorem touched_seededLinked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (left right : Cells × Padding)
    (hagree : ∀ node, RedrawCell.seedAndRoot node → left.1 node = right.1 node) :
    seededLinked adversary prfSeed publicSeed left =
      seededLinked adversary prfSeed publicSeed right := by
  rw [seededLinked, seededLinked,
    TouchedKeys.touched_honestLinked adversary prfSeed publicSeed left right hagree,
    hagree Node.secretSeed (Or.inl rfl)]

/-! ## The two handlers the charge compares -/

/-- The handler that files, at total availability: the lenient side. -/
noncomputable def lenientImpl (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  servingProgram publicSeed (keysOf prfSeed publicSeed table).2 (fun _ _ => True) table

/-- The handler that files, at the availability the carrier's served set determines. -/
noncomputable def strictImpl [HasQuery HashSpec Id] (prfSeed publicSeed : Digest)
    (table : Cells × Padding) : QueryImpl OracleWorld (StateT HandlerState ProbComp) :=
  servingProgram publicSeed (keysOf prfSeed publicSeed table).2
    (fun cache node => Available
      (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
      (ServingCarrier.disclosedAt cache) node) table

/-- **The lenient handler satisfies the facts.** At total availability the closure and the
blindness are both trivial. -/
theorem facts_lenientImpl (prfSeed publicSeed : Digest) :
    TableFacts publicSeed (fun _ _ _ => True) (fun index => ¬ RedrawCell.seedAndRoot index)
      (lenientImpl prfSeed publicSeed) :=
  tableFacts_servingProgram_keysOf prfSeed publicSeed (fun _ _ _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => rfl)

/-- **The strict handler satisfies them**, off the seed and the root: its key reads the root
cell and its availability reads the seed cell, and `allowed` excludes exactly those two. -/
theorem facts_strictImpl [HasQuery HashSpec Id] (prfSeed publicSeed : Digest) :
    TableFacts publicSeed
      (fun table cache node => Available
        (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
        (ServingCarrier.disclosedAt cache) node)
      (fun index => ¬ RedrawCell.seedAndRoot index) (strictImpl prfSeed publicSeed) :=
  tableFacts_servingProgram_keysOf prfSeed publicSeed
    (honestAvailableAt publicSeed ServingCarrier.disclosedAt)
    (fun _ carrier _ hchildren =>
      available_of_children_available _ (ServingCarrier.disclosedAt carrier) hchildren)
    (availBlind_honestAvailableAt publicSeed ServingCarrier.disclosedAt)

/-- **And the two are a lenient pair.** -/
theorem lenient_pair [HasQuery HashSpec Id] (prfSeed publicSeed : Digest) :
    Lenient publicSeed
      (fun table cache node => Available
        (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
        (ServingCarrier.disclosedAt cache) node)
      (lenientImpl prfSeed publicSeed) (strictImpl prfSeed publicSeed) :=
  lenient_servingProgram_keysOf prfSeed publicSeed
    (honestAvailableAt publicSeed ServingCarrier.disclosedAt)

/-! ## The charge -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The charge, composed.** Every hypothesis is discharged from this half's own chain: the
handlers and their facts from `ServingTable`, monotonicity from `CarrierAvailability`, blindness
from `TouchedKeys` at `RedrawCell.seedAndRoot`, availability of the root from
`RedrawCell.open_seedAndRoot`, and the reveal count off the carried seed.

What is left on the right is what the half still owes: an expected count of the probes in the
class `keep` names, and the seed-guessing avenue beside it. -/
theorem prob_charged_seededLinked [HasQuery HashSpec Id] (adversary : Adversary)
    (prfSeed publicSeed : Digest) (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (inner : HandlerState) (hinner : inner.2.1 = [])
    (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (SeededValue × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (HandlerLenient.sensitiveFlagged publicSeed
          (fun table cache node => Available
            (GraphStakes.honestRevealed (table.1 Node.secretSeed) publicSeed)
            (ServingCarrier.disclosedAt cache) node) (lenientImpl prfSeed publicSeed)
          (cells, pad)) (seededLinked adversary prfSeed publicSeed (cells, pad))).run
          (inner, false)
        pure (result, cells))] ≤
      (∑' z : SeededValue × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (strictImpl prfSeed publicSeed (cells, pad)))
              (seededLinked adversary prfSeed publicSeed (cells, pad))).run (inner, false))] *
            (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (SeededValue × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node => ¬ Available
                (GraphStakes.honestRevealed pair.1.1.2 publicSeed)
                (ServingCarrier.disclosedAt cache) node) pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl prfSeed publicSeed (cells, pad)))
            (seededLinked adversary prfSeed publicSeed (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  CarrierAvailability.prob_game_sensitive_carrier_le_canonical publicSeed
    (lenientImpl prfSeed publicSeed) (strictImpl prfSeed publicSeed)
    (facts_lenientImpl prfSeed publicSeed) (facts_strictImpl prfSeed publicSeed)
    (lenient_pair prfSeed publicSeed) stall (seededLinked adversary prfSeed publicSeed)
    RedrawCell.seedAndRoot (fun _ hnode => hnode)
    (touched_seededLinked adversary prfSeed publicSeed)
    (fun value => GraphStakes.honestRevealed value.2 publicSeed)
    (fun value => GraphStakes.honestRevealed_le value.2 publicSeed)
    (fun table value hvalue => by
      rw [seed_of_mem_support adversary prfSeed publicSeed table value hvalue])
    (fun node htouch hne value cache =>
      RedrawCell.open_seedAndRoot (GraphStakes.honestRevealed value.2 publicSeed)
        (GraphStakes.honestRevealed_le value.2 publicSeed)
        (ServingCarrier.disclosedAt cache) node htouch hne)
    inner hinner keep hkeep

end SlhDsaSecurity.ChargedHalf

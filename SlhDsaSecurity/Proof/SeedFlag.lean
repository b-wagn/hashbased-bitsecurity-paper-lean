import SlhDsaSecurity.Proof.RecordInvariant
import SlhDsaSecurity.Proof.RandomizerGate

/-!
# The flag the game hop is taken at

The hop that carries the seed charge from the blind order to the real one compares two fused
handlers that part company only at one kind of query: the adversary asking at a `PRF_msg` input
at the real seed. `HandlerComparison.prob_bad_eq` needs that query to set a **sticky flag on the
handler's state**, and this file is the flag.

**It is already in the state, which is why nothing has to be added to carry it.** The fused
handler threads the recording writer through its own state, so the adversary's record is
`(Multiplicative.toAdd state.1).2` — a component of `ω × SigningLog × S` rather than something
recovered from the value at the end. That is the same accident of presentation that made the
ordering charge readable at the carrier: the writer is in the state because a bracketed game is
not one computation.

**And it is sticky for the reason the accumulator is monotone.** A step multiplies the writer by
what it gained (`RecordInvariant.fuseServing_step_accumulates`), and a product's record component
is a multiset sum, so nothing already recorded can leave. No hypothesis about either handler is
needed — in particular none about the signer, which matters because the two handlers being
compared differ in exactly that.

**What this does not do.** The flag is defined and shown sticky; the comparison itself, its
relation and its `transfer` are the next piece. Stated separately because stickiness is the one
part that holds for *any* fused handler, and so is proved once rather than twice.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SeedFlag

open Security RecordedQueries PhaseFusion

variable {S : Type}

/-- **The flag**: the adversary's record, as the fused handler carries it, holds an input of the
`PRF_msg` class at the real seed. -/
def RecordFlag (prfSeed : Digest) (state : Multiplicative Tally × SigningLog × S) : Prop :=
  ∃ input ∈ (Multiplicative.toAdd state.1).2, RandomizerGate.PrfClass prfSeed input

/-- **The writer only gains**, read at the record component. -/
theorem record_le_of_mul (first second : Multiplicative Tally) :
    (Multiplicative.toAdd first).2 ≤ (Multiplicative.toAdd (first * second)).2 := by
  show (Multiplicative.toAdd first).2 ≤
    (Multiplicative.toAdd first + Multiplicative.toAdd second).2
  exact Multiset.le_add_right _ _

/-- **The flag is sticky**, for any fused handler and any signer. The comparison needs this of
both sides, and it costs nothing to have it of all of them. -/
theorem recordFlag_sticky (prfSeed : Digest)
    (outer : QueryImpl OracleWorld (StateT S ProbComp))
    (inner : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (Multiplicative Tally) (StateT SigningLog (OracleComp OracleWorld))))
    (before : Message → S → S) (afterMap : S → S)
    (queried : (OracleWorld + SigningSpec).Domain)
    (state : Multiplicative Tally × SigningLog × S)
    (hflag : RecordFlag prfSeed state)
    (step : (OracleWorld + SigningSpec).Range queried ×
      (Multiplicative Tally × SigningLog × S))
    (hstep : step ∈ support (((fuseServing outer inner before afterMap) queried).run state)) :
    RecordFlag prfSeed step.2 := by
  obtain ⟨input, hmem, hclass⟩ := hflag
  obtain ⟨gained, hgained⟩ := RecordInvariant.fuseServing_step_accumulates outer inner before
    afterMap queried state step hstep
  refine ⟨input, ?_, hclass⟩
  rw [hgained]
  exact Multiset.mem_of_le (record_le_of_mul state.1 gained) hmem

end SlhDsaSecurity.SeedFlag

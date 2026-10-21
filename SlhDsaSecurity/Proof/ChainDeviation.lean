import SlhDsaSecurity.Proof.Hashing

/-!
# Walking a forged chain down to its first deviation

The WOTS extraction does not hand back a collision. `Extraction.WotsPreimage.exists_preimage_witness`
gives a *preimage*: on some chain the forged value, hashed forward a positive number of steps,
reaches the honestly revealed value. That is not yet an event the structural charge can pay
for, because the charge is about a query whose answer hits an honest cell, and a preimage
says only that the two chains meet somewhere.

The gap closes by walking down the chain. Either the forged value already equals the honest
chain value at its own position — in which case the adversary holds a chain value below what
any signature revealed, and that is a secret-side win, not a structural one — or the two
chains differ somewhere and then join, and at the joining step there is a query whose answer
is the honest cell with a child that is not the honest child. That is exactly the single-child
shape of `CollisionToDeviating.deviatingCollision_of_single_child`.

The lemma below is that dichotomy with the WOTS specifics stripped out: an arbitrary
position-indexed step function against an arbitrary honest sequence. Keeping it abstract is
deliberate — the same walk serves any chain-shaped construction, and nothing in the argument
uses the width, the checksum, or the address format.
-/

namespace SlhDsaSecurity.ChainDeviation

/-- Iterating a position-indexed step, starting at `start` and advancing `length` times. -/
def fold (step : Nat → Digest → Digest) : Nat → Nat → Digest → Digest
  | _, 0, value => value
  | start, length + 1, value => fold step (start + 1) length (step start value)

@[simp] theorem fold_zero (step : Nat → Digest → Digest) (start : Nat) (value : Digest) :
    fold step start 0 value = value := rfl

theorem fold_succ (step : Nat → Digest → Digest) (start length : Nat) (value : Digest) :
    fold step start (length + 1) value = fold step (start + 1) length (step start value) := rfl

/-- **A forged chain that rejoins the honest one either starts honest or deviates first.**

If advancing `value` from `start` by `length > 0` steps lands on `honest (start + length)`,
then either `value` is already the honest value at `start`, or there is a position strictly
inside the walk at which the running value differs from the honest one yet the next step
lands exactly on the honest successor. -/
theorem fold_eq_honest (step : Nat → Digest → Digest) (honest : Nat → Digest) :
    ∀ (length start : Nat) (value : Digest), 0 < length →
      fold step start length value = honest (start + length) →
        value = honest start ∨
          ∃ position, start ≤ position ∧ position < start + length ∧
            fold step start (position - start) value ≠ honest position ∧
            step position (fold step start (position - start) value) = honest (position + 1) := by
  intro length
  induction length with
  | zero => intro _ _ hlength; exact absurd hlength (by omega)
  | succ remaining ih =>
    intro start value _ hend
    rcases Nat.eq_zero_or_pos remaining with hzero | hpos
    · -- A single step: it either started honest or deviated right here.
      subst hzero
      rw [fold_succ, fold_zero] at hend
      by_cases hstart : value = honest start
      · exact Or.inl hstart
      · exact Or.inr ⟨start, le_rfl, by omega, by simpa using hstart, by simpa using hend⟩
    · -- More than one step: look at the tail first.
      rw [fold_succ] at hend
      have htail := ih (start + 1) (step start value) hpos (by rw [hend]; ring_nf)
      rcases htail with hhonest | ⟨position, hlow, hhigh, hdiffers, hlands⟩
      · -- The tail was honest throughout, so any deviation is at the very first step.
        by_cases hstart : value = honest start
        · exact Or.inl hstart
        · refine Or.inr ⟨start, le_rfl, by omega, by simpa using hstart, ?_⟩
          simpa using hhonest
      · -- The tail already deviates; carry that position outward.
        refine Or.inr ⟨position, by omega, by omega, ?_, ?_⟩
        · rwa [show position - start = (position - (start + 1)) + 1 from by omega, fold_succ]
        · rw [show position - start = (position - (start + 1)) + 1 from by omega, fold_succ]
          exact hlands

end SlhDsaSecurity.ChainDeviation

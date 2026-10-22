import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.Assembly

/-!
# The bar a proposed attack has to clear

`HasTotalSecurityBits .strong 127` is `∀ q, ∀ adversary, … → totalAdvantage ≤ q / 2 ^ 127`, so
its negation is `∃ q, ∃ adversary`: a refutation needs **one** adversary at **one** operating
point, and nothing about how its advantage scales. This file states the arithmetic bar such an
adversary has to clear, so that a proposed attack contradicts a **statement** rather than an
argument.

**The scale.** `SecretGuessCharge.prob_single_guess` is an *equality*: one staked guess at a
`128`-bit secret is exactly `2 ^ -128`. And `Assembly.half_add_half` says the target is exactly
**two** of those. So an adversary that stakes at most `2 * q` guesses over `q` queries is inside
the target, and a refutation must convert **more than two staked guesses per query** into
forgery probability.

**Why two is the interesting number here.** `Hashing.message_randomizer_overlap` makes one
oracle query at `x ‖ PK.seed ‖ PK.root ‖ m` simultaneously an `H_msg` query at randomiser `x`
and a `PRF_msg` query at `prf = x`, so the *syntactic* count is two readings per query. The
reduction charges both at the full rate, which is where its factor comes from.

**What this file does not say.** It does not say the second reading fails to convert. That
argument is about what an adversary can do with `SK.prf` — `Scheme.verifyInternal` computes the
digest from `signature.randomizer`, a field the forger supplies, and never reads `SK.prf` — and
it is cryptographic reasoning this development has no model in which to state. The bar below is
the part that *is* arithmetic, and it is stated so the other part can be argued against
something fixed.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.GuessingBar

/-- **Two staked guesses per query is exactly the target.** `Assembly.half_add_half` with the
two halves written as one numerator. -/
theorem two_stakes_eq_target (queries : Nat) :
    ((2 * queries : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) =
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [← Assembly.half_add_half queries, ENNReal.div_add_div_same]
  push_cast
  ring_nf

/-- **The bar.** An adversary whose staked guesses number at most `2 * q` is inside
`q / 2 ^ 127`, whatever `q` is and whatever the guesses are. A refutation of
`HasTotalSecurityBits .strong 127` at budget `q` must therefore convert **more** than `2 * q`
staked guesses into forgery probability — one operating point suffices, but that one point has
to beat this. -/
theorem within_target_of_stakes (queries : Nat) (inputs : Finset Bytes)
    (guessOf : Bytes → Digest) (hstakes : inputs.card ≤ 2 * queries) :
    Pr[fun secret : Digest => ∃ input ∈ inputs, guessOf input = secret |
      ($ᵗ Digest : ProbComp Digest)] ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  refine le_trans (SecretGuessCharge.prob_secret_guessed_le inputs guessOf) ?_
  rw [← two_stakes_eq_target queries]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hstakes) _

/-- **And one stake per query is half of it**, which is what the ordinary guessing adversary
gets: `q` queries, `q` guesses, `q / 2 ^ 128`. The gap between this and the bar is the whole of
what a refutation has to find. -/
theorem one_stake_is_half (queries : Nat) (inputs : Finset Bytes) (guessOf : Bytes → Digest)
    (hstakes : inputs.card ≤ queries) :
    Pr[fun secret : Digest => ∃ input ∈ inputs, guessOf input = secret |
      ($ᵗ Digest : ProbComp Digest)] +
        Pr[fun secret : Digest => ∃ input ∈ inputs, guessOf input = secret |
          ($ᵗ Digest : ProbComp Digest)] ≤
      (queries : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [← Assembly.half_add_half queries]
  exact add_le_add
    (le_trans (SecretGuessCharge.prob_secret_guessed_le inputs guessOf)
      (ENNReal.div_le_div_right (Nat.cast_le.mpr hstakes) _))
    (le_trans (SecretGuessCharge.prob_secret_guessed_le inputs guessOf)
      (ENNReal.div_le_div_right (Nat.cast_le.mpr hstakes) _))

end SlhDsaSecurity.GuessingBar

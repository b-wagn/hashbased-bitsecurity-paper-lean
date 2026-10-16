import VCVio.OracleComp.ProbComp

/-!
# Bit security

Definitions 3 and 4 of the manuscript, for any security game whose experiment outputs whether the
adversary wins together with a count per kind of query.

A security game for a type `Scheme` of schemes has a type of adversaries and, for each scheme and
each adversary, its experiment: a probabilistic computation returning the winning bit and, for
every kind `k` of query, the number of queries of kind `k` made during the experiment. Which
kinds exist is part of the game; for unforgeability they are the adversary's signing queries and
own hash queries, and the hash queries of key generation, of the signer, and of the final
verification (`Security/SUFCMA.lean`).

A counting mode `Z` is a set of kinds. The work of the adversary in mode `Z` is the sum of the
counts of the kinds in `Z`. The adversary makes at most `q` many `Z`-queries if its work in mode
`Z` is at most `q` with probability 1, that is, for every choice of the experiment's randomness
(a worst-case bound, not an expectation).

The game has `bits` bits of classical security for a scheme in counting mode `Z` if every
adversary making at most `q ≥ 1` many `Z`-queries wins with probability at most `q / 2^bits`. In
other words, the work-to-success ratio `q / Pr[win]` of every adversary is at least `2^bits`. The
bound is required only for `q ≥ 1`: otherwise an adversary doing no counted work, which may still
win with tiny positive probability by guessing, would rule out every number of bits.

It has exactly `bits` bits of classical security if it has `bits` bits but not `bits + 1` bits:
some adversary making at most `q ≥ 1` many `Z`-queries wins with probability more than
`q / 2^(bits + 1)`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- A security game for schemes of type `Scheme`, counting queries of the kinds in `Kind`. -/
structure SecurityGame (Scheme : Type) (Kind : Type) where
  /-- The adversaries of the game. -/
  Adversary : Type
  /-- The experiment of an adversary against a scheme: whether it wins, and the number of
  queries of each kind made during the experiment. -/
  experiment : Scheme → Adversary → ProbComp (Bool × (Kind → ℕ))

namespace SecurityGame

variable {Scheme Kind : Type} (game : SecurityGame Scheme Kind) (scheme : Scheme)

/-- The probability that the adversary wins. -/
noncomputable def advantage (adversary : game.Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | game.experiment scheme adversary]

/-- The adversary makes at most `q` many `Z`-queries: with probability 1, the counts of the kinds
in the counting mode `Z` sum to at most `q`. -/
def HasQueryBound (Z : Finset Kind) (adversary : game.Adversary) (q : ℕ) : Prop :=
  Pr[fun result => ∑ kind ∈ Z, result.2 kind ≤ q | game.experiment scheme adversary] = 1

/-- `bits` bits of classical security in counting mode `Z`: every adversary making at most
`q ≥ 1` many `Z`-queries wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, game.HasQueryBound scheme Z adversary q →
    game.advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- Exactly `bits` bits of classical security in counting mode `Z`: `bits` bits (a security
proof), but not `bits + 1` bits (an attack). -/
def HasExactClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  game.HasClassicalSecurityBits scheme Z bits ∧
    ¬ game.HasClassicalSecurityBits scheme Z (bits + 1)

end SecurityGame

end XmssSecurity

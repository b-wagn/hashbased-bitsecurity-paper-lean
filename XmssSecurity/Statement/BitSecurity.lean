import VCVio.OracleComp.ProbComp

/-!
# Bit security

A game returns a winning bit and a count for each query kind. A counting mode `Z` selects
which counts contribute to work. For every budget `q ≥ 1`, an adversary whose work is at most
`q` with probability one must win with probability at most `q / 2^bits`.

The budget is a worst-case bound, not an expectation. Requiring `q ≥ 1` allows a positive
guessing probability even when no work is counted. An exact level holds at `bits` and fails
at `bits + 1`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- A security game for schemes of type `Scheme`, counting queries of the kinds in `Kind`. -/
structure SecurityGame (Scheme : Type) (Kind : Type) where
  /-- The adversaries of the game. -/
  Adversary : Type
  /-- The winning bit and query counts. -/
  experiment : Scheme → Adversary → ProbComp (Bool × (Kind → ℕ))

namespace SecurityGame

variable {Scheme Kind : Type} (game : SecurityGame Scheme Kind) (scheme : Scheme)

/-- The probability that the adversary wins. -/
noncomputable def advantage (adversary : game.Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | game.experiment scheme adversary]

/-- The total count in mode `Z` is at most `q` with probability one. -/
def HasQueryBound (Z : Finset Kind) (adversary : game.Adversary) (q : ℕ) : Prop :=
  Pr[fun result => ∑ kind ∈ Z, result.2 kind ≤ q | game.experiment scheme adversary] = 1

/-- A work factor `K`: every adversary with budget `q ≥ 1` wins with probability at most `q / K`.
This also expresses bounds between integer bit levels; the bit level is `log₂ K`. -/
def HasClassicalSecurityBound (Z : Finset Kind) (workFactor : ℝ≥0∞) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, game.HasQueryBound scheme Z adversary q →
    game.advantage scheme adversary ≤ q / workFactor

/-- Every adversary with budget `q ≥ 1` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, game.HasQueryBound scheme Z adversary q →
    game.advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- A security proof and an attack whose work factors differ by less than a factor of two,
i.e. less than one bit. The bounds need not be powers of two. -/
def HasTightClassicalSecurityBounds (Z : Finset Kind) (lower upper : ℝ≥0∞) : Prop :=
  0 < lower ∧ upper < 2 * lower ∧
    game.HasClassicalSecurityBound scheme Z lower ∧
      ¬game.HasClassicalSecurityBound scheme Z upper

/-- Security at `bits`, but not at `bits + 1`. -/
def HasExactClassicalSecurityBits (Z : Finset Kind) (bits : ℕ) : Prop :=
  game.HasClassicalSecurityBits scheme Z bits ∧
    ¬ game.HasClassicalSecurityBits scheme Z (bits + 1)

end SecurityGame

end XmssSecurity

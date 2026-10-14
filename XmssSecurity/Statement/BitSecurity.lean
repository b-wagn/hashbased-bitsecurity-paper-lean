import VCVio.OracleComp.ProbComp

/-!
# Bit security

A security notion for a type `Scheme` of schemes is a type of adversaries together with, for each
scheme and each adversary, its experiment: a probabilistic computation returning whether the
adversary wins and the number of queries charged to it. Which queries are charged is part of the
notion and is documented with each notion.

The notion has `bits` bits of classical security for a scheme if every adversary charged at most
`q ≥ 1` queries on every execution of the experiment (a worst-case bound over the support, not
an expectation) wins with probability at most `q / 2^bits`. In other words, the work-to-success
ratio `q / Pr[win]` of every adversary is at least `2^bits`.

It has exactly `bits` bits of classical security if it has `bits` bits but not `bits + 1` bits:
some adversary charged at most `q ≥ 1` queries wins with probability more than `q / 2^(bits + 1)`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-- A security notion for schemes of type `Scheme`. -/
structure SecurityNotion (Scheme : Type) where
  /-- The adversaries of the notion. -/
  Adversary : Type
  /-- The experiment of an adversary against a scheme: whether it wins, and the number of
  queries charged to it. -/
  experiment : Scheme → Adversary → ProbComp (Bool × ℕ)

namespace SecurityNotion

variable {Scheme : Type} (notion : SecurityNotion Scheme) (scheme : Scheme)

/-- The probability that the adversary wins. -/
noncomputable def advantage (adversary : notion.Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | notion.experiment scheme adversary]

/-- Every execution of the experiment charges at most `q` queries. -/
def HasQueryBound (adversary : notion.Adversary) (q : ℕ) : Prop :=
  ∀ result ∈ support (notion.experiment scheme adversary), result.2 ≤ q

/-- `bits` bits of classical security: every adversary with a query bound `q ≥ 1` wins with
probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : ℕ) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, notion.HasQueryBound scheme adversary q →
    notion.advantage scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)

/-- Exactly `bits` bits of classical security: `bits` bits (a security proof), but not
`bits + 1` bits (an attack). -/
def HasExactClassicalSecurityBits (bits : ℕ) : Prop :=
  notion.HasClassicalSecurityBits scheme bits ∧
    ¬ notion.HasClassicalSecurityBits scheme (bits + 1)

end SecurityNotion

end XmssSecurity

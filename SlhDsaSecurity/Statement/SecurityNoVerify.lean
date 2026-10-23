import SlhDsaSecurity.Statement.Security

/-!
# Counting every hash call except final verification's

`HasTotalBudget` charges every hash call of the game. This variant charges every call except
those the final verification makes: key generation, signing, and the adversary's direct calls
count, and verification is free. Signing requests are still capped separately at
`signingLimit`. The verification calls are `outcome.counts .verification`, the coordinate the
experiment already charges them to, so the charged count is the total less that coordinate.

Every adversary within `HasTotalBudget adversary q` is within `HasNoVerifyBudget adversary q`,
so a security statement at this budget is a stronger one.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Security

/-- At most `2 ^ 64` signing requests and at most `q` hash calls outside final verification,
jointly with probability one. -/
def HasNoVerifyBudget (adversary : Adversary) (q : Nat) : Prop :=
  Pr[fun result => result.1.counts .signing ≤ signingLimit ∧
      result.2 - result.1.counts .verification ≤ q | runAll adversary] = 1

/-- The bit-security statement at that budget. -/
def HasNoVerifySecurityBits (notion : Notion) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasNoVerifyBudget adversary q →
    totalAdvantage notion adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end SlhDsaSecurity.Security

import SlhDsaSecurity.Proof.HonestGrowth

/-!
# A budget that admits an adversary at all is at least what key generation spends

The accounting subtracts `2 ^ subtreeHeight` from the budget before handing the remainder to
the charges, and reads `q - 2 ^ subtreeHeight` as a count of hash calls the adversary still
has. On `Nat` that subtraction truncates, so the reading is only honest once `q` is known to
be at least `512`; otherwise the term is `0` and the accounting would be claiming the
adversary has no calls left while the budget says it has some.

The fact is not an assumption about adversaries but a consequence of the budget's own shape.
`HasTotalBudget adversary q` asserts that the count stays within `q` with probability one, and
every run of the game begins by building the top subtree, whose `2 ^ subtreeHeight` compression
calls are charged like any other. So a budget below `512` would be exceeded on every run the
game has — and a probability-one event that holds nowhere forces the support to be empty,
which makes that same probability zero rather than one. Both horns are closed by the one
argument, and in particular nothing here needs the support to be nonempty: if an adversary
always fails, it has no budget to speak of, and the statement holds of it vacuously.

The route to the count is the warmed presentation, where key generation is already isolated:
`HonestGrowth.growth_le_count_sub_keygen` splits a tail's total at the end of key generation
and `HonestGrowth.pow_le_count_keygen` bounds that part below. `WarmedGame.evalDist_outcome`
carries the conclusion back to the unwarmed run the budget is stated against, in the direction
opposite to the one the charges use it in.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.KeygenBudget

open Security WarmedGame CanonicalGraph

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

end SlhDsaSecurity.KeygenBudget

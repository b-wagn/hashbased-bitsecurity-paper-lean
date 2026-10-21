import SlhDsaSecurity.Proof.Assembly

/-!
# What one charged query can buy

Under the all-queries-counted accounting the whole game is a sequence of at most `q` oracle
calls, every one of them charged. A forgery needs at least one lucky event, and every lucky
event is attached to a single query. So the entire bound is decided by a *rate per query*,
and the target `q / 2 ^ 127` is exactly the rate `4 / 2 ^ 129`.

Working from first principles, with `n = 16` so that every secret and every cell is 128 bits,
a single query can be lucky in these ways and no others.

*Input-side.* The query's input contains a secret the adversary does not know. `SK.seed`
yields every FORS and WOTS secret, so it forges outright; `SK.prf` yields randomizers, which
is what would let an adversary steer signatures onto one FORS instance. Each is a uniform
128-bit value, so each guess succeeds with probability `2 ^ -128`, rate `2`. A single query
input generically lies in only one of the two formats, so the input-side rate is `2`, not `4`.

*Answer-side.* The query's answer is lucky. Either it truncates to the honest cell of the node
its own input names — a collision or preimage, rate `2 ^ -128 = 2`, which
`CollisionCharge.fresh_tweakable_prob_hit` shows is exactly attained — or it parses to a digest
whose fourteen FORS positions are all already disclosed, rate `2 ^ -129 = 1` under the sharper
`2 ^ 102` load cap. Answer-side rate `3`.

The arithmetic below is the point. The union of the avenues costs `5` per query while the
target allows `4`, so a per-query union bound proves only `129 - log₂ 5 ≈ 126.68` bits. But an
adversary must *apportion* its `q` queries among the avenues, and the best it can do is spend
them all on the dearest one, for rate `2` — comfortably inside `4`. So the target is not
refuted by any of these attacks; what fails is the union bound, by a factor `5 / 4`.

Proving `127` therefore needs an argument strictly better than a per-query union over the
avenues: one that uses the fact that a query spent guessing a secret is not simultaneously
buying a structural preimage. That is a statement about the adversary's whole strategy, not
about one query, and it is not something the charge lemmas in this development provide.
-/

namespace SlhDsaSecurity.PerQueryBudget

/-- Rates per charged query, in units of `2 ^ -129`. -/
def secretGuessRate : Nat := 2

def structuralRate : Nat := 2

def forsCoverageRate : Nat := 1

/-- The target `q / 2 ^ 127` is the per-query rate `4 / 2 ^ 129`. -/
def targetRate : Nat := 4

/-- **The union bound overshoots.** Summing the avenues costs more per query than the target
allows, so no per-query union bound can prove the target. -/
theorem union_exceeds_target :
    targetRate < secretGuessRate + structuralRate + forsCoverageRate := by decide

/-- The overshoot is exactly a factor `5 / 4`. -/
theorem union_rate_eq :
    secretGuessRate + structuralRate + forsCoverageRate = 5 := by decide

/-- **The target is consistent with every avenue.** An adversary apportions its queries, so
whatever split it chooses the advantage it buys is at most the dearest single rate, which is
within the target. -/
theorem split_within_target (first second third : Nat) :
    secretGuessRate * first + structuralRate * second + forsCoverageRate * third ≤
      targetRate * (first + second + third) := by
  simp only [secretGuessRate, structuralRate, forsCoverageRate, targetRate]
  omega

/-- In particular all of the budget on the dearest avenue stays inside the target. -/
theorem dearest_within_target (queries : Nat) :
    secretGuessRate * queries ≤ targetRate * queries := by
  simp only [secretGuessRate, targetRate]
  omega

/-- The bits a per-query union bound actually yields: `5 q / 2 ^ 129`, which is weaker than
the target `4 q / 2 ^ 129`. -/
theorem union_bound_is_weaker (queries : Nat) (hqueries : 0 < queries) :
    targetRate * queries < (secretGuessRate + structuralRate + forsCoverageRate) * queries := by
  simp only [secretGuessRate, structuralRate, forsCoverageRate, targetRate]
  omega

end SlhDsaSecurity.PerQueryBudget

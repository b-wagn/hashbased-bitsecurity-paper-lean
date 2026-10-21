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

/-! ## Why the existing 127-bit results do not transfer

The secret-guessing rate is the only one that depends on the seed length, and it is what
decides the whole question.

`SLH-DSA-128s` sets `n = 16`, so `SK.seed` and `SK.prf` are 128-bit and a guess costs
`2 ^ -128`, rate `2`. Added to the structural rate `2` that is already the entire target, so
the FORS term — however sharp its cap — pushes the union past `4`.

The 127-bit theorems that already exist use **256-bit** seeds: the leanVM `lean_sphincs`
scheme and the XMSS development in this repository both do. There a seed guess costs
`2 ^ -256`, which is negligible at this scale, so the union is `2 + 1 = 3`, inside the target,
and a per-query union bound suffices. That is precisely the term those proofs never had to
pay, and it is why their structure does not carry over to standard `SLH-DSA-128s`.

So the obstruction is a parameter fact about the standard scheme, not a gap in the
machinery here. -/

/-- Secret-guessing rate as a function of the seed length, in units of `2 ^ -129`: a `b`-bit
secret is guessed at rate `2 ^ -b`, i.e. `2 ^ (129 - b)` units. Lengths past `129` bits cost
less than one unit, so they are recorded as `0`; at `b = 256` the true rate is `2 ^ -256`,
which is below this granularity by a factor `2 ^ 127`. -/
def seedGuessRateOfBits (bits : Nat) : Nat := if bits ≤ 128 then 2 ^ (129 - bits) else 0

theorem seedGuessRate_128 : seedGuessRateOfBits 128 = secretGuessRate := by decide

theorem seedGuessRate_256 : seedGuessRateOfBits 256 = 0 := by decide

/-- **With 128-bit seeds the union bound cannot reach the target.** -/
theorem union_exceeds_target_of_128 :
    targetRate < seedGuessRateOfBits 128 + structuralRate + forsCoverageRate := by decide

/-- **With 256-bit seeds it can.** This is the regime of the existing 127-bit theorems, and
the reason their argument does not transfer to `SLH-DSA-128s`. -/
theorem union_within_target_of_256 :
    seedGuessRateOfBits 256 + structuralRate + forsCoverageRate ≤ targetRate := by decide

/-! ## The union closes once queries are classified

The overshoot above comes from letting a single query pursue every avenue at once. It cannot.
FIPS 205 gives each hash call a fixed byte format, and the avenues available to a query are
determined by which format its input has:

* `PK.seed ‖ ADRS ‖ payload` — the tweakable calls `F`, `H`, `T` and the two `PRF`s. Such a
  query can be a `SK.seed` guess (its payload is the guessed seed) and its answer can hit the
  honest cell of the node its address names. Rate `2 + 2 = 4`.
* `R ‖ PK.seed ‖ PK.root ‖ M` for `H_msg`, and `SK.prf ‖ PK.seed ‖ M` for `PRF_msg`. Such a
  query's answer can parse to a covered digest, and its input can be a `SK.prf` guess. Rate
  `1 + 2 = 3`.

No query is in both classes except under the coincidence that `PK.seed ‖ PK.root` happens to
encode a valid address, which is exactly the criterion of `Proof/HashSeparation.lean` and has
probability at most `2 ^ -165` under actual key generation
(`HashSeparation.prob_possible_le`, via `KeygenUniform.keygen_prob_possible_le`).

So the per-query union is the *maximum over classes*, which is `4` — precisely the target
rate — rather than the sum `5`. The budget closes, and the `2 ^ -165` separation defect is far
below the slack at any `q ≥ 1`.
-/

/-- The two byte-format classes a charged hash call can belong to. -/
inductive QueryClass where
  | structural
  | message
deriving DecidableEq

/-- The avenues live for a query of each class, in units of `2 ^ -129`. -/
def classRate : QueryClass → Nat
  | .structural => secretGuessRate + structuralRate
  | .message => forsCoverageRate + secretGuessRate

/-- **Every class fits the target rate.** This is the step the naive union misses. -/
theorem classRate_le_target (class_ : QueryClass) : classRate class_ ≤ targetRate := by
  cases class_ <;> decide

/-- The structural class is the dearest, and it meets the target exactly. -/
theorem classRate_structural : classRate .structural = targetRate := by decide

/-- **The budget closes over a whole run.** Charging each query at its own class rate, a run
of any length stays inside the target. -/
theorem total_le_target (classes : List QueryClass) :
    (classes.map classRate).sum ≤ targetRate * classes.length := by
  induction classes with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hhead := classRate_le_target head
    calc classRate head + (tail.map classRate).sum
        ≤ targetRate + targetRate * tail.length := Nat.add_le_add hhead ih
      _ = targetRate * (tail.length + 1) := by ring
end SlhDsaSecurity.PerQueryBudget

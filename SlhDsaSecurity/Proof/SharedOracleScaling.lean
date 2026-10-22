import SlhDsaSecurity.Proof.SharedOracleArithmetic

/-!
# How the shared-oracle sketch scales, and what its certificate does and does not say

`SharedOracleArithmetic.proposed_bound_exceeds_target` certifies

    2 * work / wordSpace + 1 / 2 ^ 78 < proposedLowerBound

at `work := 2 ^ 81`, `instances := 2 ^ 63`, `setup := 2 ^ 47`. Two things about that statement
have to be separated before it is quoted, and both are settled here by elaboration rather than
by reading exponents.

**What the target is.** `target_eq_127` below: `2 * work / wordSpace` is *the same rational* as
`work / 2 ^ 127`. So the certificate's comparison really is against the 127-bit threshold at
that work level, and no exponent has been misread.

**Whether it holds for all `q`.** It does not. `lowerBoundAt` is the same expression with the
work level a parameter, and:

* `holds_at_two_pow_81` — at `2 ^ 81` the bound exceeds the threshold, which is the certificate;
* `fails_at_two_pow_100` — at `2 ^ 100` it is **below** it.

The reason is visible in the expression once the work level moves. The leading term
`2 * (work - setup) / wordSpace` is the threshold less a constant, so the entire excess comes
from the fixed bonus `rootEvent * usefulUniqueHit * recoverySuccess * continuationSuccess` —
built from `chainRequests` and `instances`, which are **constants** and do not grow with the work
level — while two of the subtracted terms do grow with it, one linearly and one as `work ^ 2`.
So the margin is a constant racing growing corrections, and it is lost well before `2 ^ 100`.

**So the claim the certificate supports is "there is an operating point at which the proposed
calculation exceeds `q / 2 ^ 127`", not "SLH-DSA-SHAKE has fewer than 127 bits of security".**
Those are different claims and only the first is certified. What would support the second is a
bound exceeding the threshold as a function of `q`, and this expression does not have that
shape: its excess over the threshold is bounded by a constant, so the ratio to the threshold
tends to one.

None of this touches the *other* obligation the sketch's own header names — that no concrete
adversary is yet shown to achieve the displayed bound.
-/

namespace SlhDsaSecurity.SharedOracleScaling

open SharedOracleArithmetic

/-- **The certificate's target is the 127-bit threshold**, as an identity of rationals rather
than a reading of exponents. -/
theorem target_eq_127 : 2 * work / wordSpace = work / 2 ^ 127 := by
  rw [work, wordSpace]; norm_num

/-- The sketch's lower bound with the work level a parameter instead of `2 ^ 81`. Every other
quantity is left exactly as the certificate fixes it. -/
def lowerBoundAt (level : ℚ) : ℚ :=
  2 * (level - setup) / wordSpace - 2 * rootEvent * recoveryCost / wordSpace -
    3 * level ^ 2 / (2 * wordSpace ^ 2) -
    (setupFailure + rootEvent * (chainRequests + recoveryCost) / wordSpace) *
      (2 * level / wordSpace) +
    rootEvent * usefulUniqueHit * recoverySuccess * continuationSuccess

set_option exponentiation.threshold 1024 in
/-- **At the certificate's own work level the bound exceeds the threshold.** -/
theorem holds_at_two_pow_81 :
    2 * (2 ^ 81 : ℚ) / wordSpace < lowerBoundAt (2 ^ 81) := by
  norm_num [lowerBoundAt, usefulUniqueHit, wordSpace, instances, setup,
    recoveryCost, rootEvent, chainRequests, setupFailure, recoverySuccess, continuationSuccess]

set_option exponentiation.threshold 1024 in
/-- **And at a higher one it does not.** So the certificate is a statement about an operating
point, not about the scheme's asymptotic security level. -/
theorem fails_at_two_pow_100 :
    lowerBoundAt (2 ^ 100) < 2 * (2 ^ 100 : ℚ) / wordSpace := by
  norm_num [lowerBoundAt, usefulUniqueHit, wordSpace, instances, setup,
    recoveryCost, rootEvent, chainRequests, setupFailure, recoverySuccess, continuationSuccess]

end SlhDsaSecurity.SharedOracleScaling

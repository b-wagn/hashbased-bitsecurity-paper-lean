import Mathlib.Tactic.NormNum

/-!
# Exact arithmetic for the shared-oracle feasibility review

These are numerical certificates for a proposed probability calculation.
They do not assert that any concrete adversary achieves the displayed lower
bound. The connection to the actual experiment is a separate obligation.
-/

namespace SlhDsaSecurity.SharedOracleArithmetic

def wordSpace : ℚ := 2 ^ 128
def instances : ℚ := 2 ^ 63
def work : ℚ := 2 ^ 81
def setup : ℚ := 2 ^ 47
def recoveryCost : ℚ := 29 * instances / 32
def rootEvent : ℚ := 1 / 256
def chainRequests : ℚ := 2 ^ 64 - 2 ^ 21
def setupFailure : ℚ := 1 / 2 ^ 40
def recoverySuccess : ℚ := 31 / 32 - 1 / 2 ^ 50
def continuationSuccess : ℚ := 99 / 100

/-- Sixty-four-row chains retain sixty-three useful positions each. -/
def usefulUniqueHit : ℚ :=
  (63 * chainRequests / (64 * wordSpace)) * (1 - (chainRequests - 1) / wordSpace)

/-- Conservative assembly including setup, spent detection queries, quadratic
inversion loss, and loss of the baseline on every accepted recovery candidate. -/
def proposedLowerBound : ℚ :=
  2 * (work - setup) / wordSpace - 2 * rootEvent * recoveryCost / wordSpace -
    3 * work ^ 2 / (2 * wordSpace ^ 2) -
    (setupFailure + rootEvent * (chainRequests + recoveryCost) / wordSpace) *
      (2 * work / wordSpace) +
    rootEvent * usefulUniqueHit * recoverySuccess * continuationSuccess

set_option exponentiation.threshold 1024 in
theorem proposed_bound_exceeds_target :
    2 * work / wordSpace + 1 / 2 ^ 78 < proposedLowerBound := by
  norm_num [proposedLowerBound, usefulUniqueHit, wordSpace, instances, work, setup,
    recoveryCost, rootEvent, chainRequests, setupFailure, recoverySuccess, continuationSuccess]

theorem signing_allowance :
    (2 ^ 20 : Nat) + (2 ^ 64 - 2 ^ 21) + 2 ^ 20 = 2 ^ 64 := by norm_num

theorem total_work_cap :
    (2 ^ 47 : Nat) + 29 * 2 ^ 58 + 3 * 2 ^ 79 + 2 ^ 68 + 3824 < 2 ^ 81 := by norm_num

theorem baseline_setup_cap :
    (2 ^ 20 : Nat) + 512 * 3824 + 2 ^ 20 + 3824 + (2 ^ 46 + 1) +
      35 * 15 + 3824 < 2 ^ 47 := by norm_num

theorem maximum_frame_length : (1024 : Nat) + 16 * (64 - 1) = 2032 := by norm_num

set_option exponentiation.threshold 1024 in
theorem occupied_mean_certificate : (17 / 128 : ℚ) < (63 / 64) ^ 128 := by norm_num

theorem admissible_checksum_tail : (527 / 6125 : ℚ) < 1 / 8 := by norm_num

set_option exponentiation.threshold 1024 in
theorem eligible_key_failure : (7 / 8 : ℚ) ^ 512 < 1 / 2 ^ 98 := by norm_num

/-- Rational lower bound on exp(1) suffices for both continuation tail estimates. -/
theorem continuation_certificate :
    (99 / 100 : ℚ) <
      1 - 3 / 2 ^ 15 - 57344 * (24 / 65) ^ 16 - (24 / 65) ^ 32 := by norm_num

/-! ## What charging the signing requests does to the leak term

The certificate above is stated for the **verifier-counted** experiment, where a signing request
costs nothing. `Security.HasTotalSecurityBits` — the statement actually being proved — is against
`Security.HasTotalBudget`, which charges **every** hash call in the game, signing included, and
caps requests separately at `signingLimit`. Under that accounting the chain requests have to be
paid for in `q`, and the leak term does not survive it.

Write `requests` for the chain requests and `cost` for the hashes one request spends. The leak
term is at most `rootEvent` times `requests / wordSpace`, so at most `requests / 2 ^ 136`, and it
does **not** grow with `q`: `signingLimit` caps it however large the budget. The target is
`q / 2 ^ 127`, and `q ≥ requests * cost`. So the term beats the target only if
`cost < 1 / 512` — and a signing request costs at least one hash.

`leak_term_le_target` is that, and the margin is a factor of `512` **before** any estimate of
what a signature actually costs — `cost ≥ 1` is the whole hypothesis. A per-request figure would
sharpen it, and the development does not currently bound one: `HonestGrowth.pow_le_count_keygen`
gives `2 ^ subtreeHeight` for key generation and there is no signing analogue, so any larger
number here would be asserted rather than cited.

**This does not refute the certificate.** The certificate is arithmetic about a proposed
calculation in the experiment it names, and it remains correct there. What it says is that the
leak term cannot be the thing that beats `q / 2 ^ 127` once the requests producing it are
charged — the same `signingLimit`-versus-`q` confusion that has now caught two of us. -/

/-- **A term bounded by `requests / 2 ^ 136` cannot exceed `q / 2 ^ 127` once each request is
paid for.** Stated cross-multiplied, so the file keeps its minimal imports: this is
`requests / (256 * 2 ^ 128) ≤ q / 2 ^ 127`. One hash per request is enough, with a factor of
`512` to spare. -/
theorem leak_term_le_target (requests cost q : Nat) (hcost : 1 ≤ cost)
    (hbudget : requests * cost ≤ q) :
    requests * 2 ^ 127 ≤ q * (256 * 2 ^ 128) := by
  have hle : requests ≤ q :=
    le_trans (le_trans (le_of_eq (Nat.mul_one requests).symm)
      (Nat.mul_le_mul_left requests hcost)) hbudget
  calc requests * 2 ^ 127 ≤ q * 2 ^ 127 := Nat.mul_le_mul_right _ hle
    _ ≤ q * (256 * 2 ^ 128) := Nat.mul_le_mul_left _ (by norm_num)

end SlhDsaSecurity.SharedOracleArithmetic

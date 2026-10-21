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

end SlhDsaSecurity.SharedOracleArithmetic

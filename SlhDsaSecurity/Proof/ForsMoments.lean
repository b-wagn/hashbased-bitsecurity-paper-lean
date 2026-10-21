import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# Arithmetic for a possible FORS concentration argument

Touchard polynomials provide the raw moments of a Poisson load. This file checks the
polynomial values and a sixth-moment scalar inequality only. It does not establish a
Poisson coupling, a concentration theorem, or a bound for adaptive signing transcripts.
-/

namespace SlhDsaSecurity.ForsMoments

/-- A finite row avoids expanding the Stirling recurrence exponentially during kernel checks. -/
def stirlingRow : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
      let previous := stirlingRow n
      List.ofFn fun k : Fin (n + 2) =>
        k.val * previous.getD k.val 0 +
          match k.val with
          | 0 => 0
          | j + 1 => previous.getD j 0

theorem stirlingRow_getD (n k : Nat) :
    (stirlingRow n).getD k 0 = Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [stirlingRow, Nat.stirlingSecond]
  | succ n ih =>
      have ih' (j : Nat) := ih j
      simp only [List.getD_eq_getElem?_getD] at ih'
      by_cases hk : k < n + 2
      · simp only [stirlingRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk,
          dite_true, Option.getD_some]
        cases k with
        | zero => simp [Nat.stirlingSecond]
        | succ k => simp only [Nat.stirlingSecond, ih']
      · simp only [stirlingRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk,
          dite_false, Option.getD_none]
        exact (Nat.stirlingSecond_eq_zero_of_lt (by omega)).symm

def touchard (degree mean : Nat) : Nat :=
  ∑ k ∈ Finset.range (degree + 1), Nat.stirlingSecond degree k * mean ^ k

def cachedTouchard (degree mean : Nat) : Nat :=
  let row := stirlingRow degree
  ∑ k ∈ Finset.range (degree + 1), row.getD k 0 * mean ^ k

theorem touchard_eq_cached (degree mean : Nat) :
    touchard degree mean = cachedTouchard degree mean := by
  simp only [touchard, cachedTouchard, stirlingRow_getD]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exact polynomials, not a numerical approximation to a signing experiment. -/
theorem touchard_bounds :
    touchard 14 2 = 20732504062 ∧
      touchard 14 3 < 2 ^ 39 ∧ touchard 28 3 < 2 ^ 92 ∧
      touchard 42 3 < 2 ^ 151 ∧ touchard 56 3 < 2 ^ 215 ∧
      touchard 84 3 < 2 ^ 353 := by
  simp only [touchard_eq_cached]
  decide +kernel

set_option exponentiation.threshold 1024 in
/-- Scalar majorant for the four terms in the sixth centered moment of a sum.
The corresponding probabilistic identity and its hypotheses are not proved here. -/
theorem sixth_moment_scalar :
    ((2 ^ 63 : ℚ) * 2 ^ 359 +
        15 * (2 ^ 63) ^ 2 * 2 ^ 219 * 2 ^ 92 +
        10 * (2 ^ 63) ^ 2 * 2 ^ 308 +
        15 * (2 ^ 63) ^ 3 * (2 ^ 92) ^ 3) /
      ((2 ^ 63) * (2 ^ 39)) ^ 6 < 1 / 2 ^ 142 := by
  norm_num

end SlhDsaSecurity.ForsMoments

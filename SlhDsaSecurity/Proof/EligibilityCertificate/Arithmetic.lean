import Mathlib.Data.Nat.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SlhDsaSecurity.EligibilityCertificate

def fastPow (a : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | f+1, n =>
    let p := fastPow a f (n/2)
    if n%2=0 then p*p else p*p*a

def pow2 (n : Nat) := fastPow 2 32 n

def weight (a : Nat) : Nat :=
  #[16,15,15,14,14,13,13,12,12,11,10,9,8,6,4,0][a]!

def digitPolynomial (start : Nat) : Nat :=
  (List.ofFn fun a : Fin (16-start) =>
    pow2 (142 * ((a.val+start) + 481 * weight (a.val+start)))).sum

def filterCode : Nat :=
  pow2 (142*256) * ((pow2 (142*65)-1)/(pow2 142-1)) *
    ((pow2 (142*(481*145))-1)/(pow2 (142*481)-1))

def count : Nat :=
  ((digitPolynomial 0 ^ 32 * filterCode) / pow2 (142*(481*512+480))) % pow2 142 -
  ((digitPolynomial 1 ^ 32 * filterCode) / pow2 (142*(481*512+480))) % pow2 142

theorem count_value : count = 51836437762795907552969185927258758790 := by
  decide +kernel

theorem count_gt : 2^125 < count := by rw [count_value]; decide +kernel

theorem fastPow_eq (a fuel exponent : Nat) (h : exponent < 2^fuel) :
    fastPow a fuel exponent = a^exponent := by
  induction fuel generalizing exponent with
  | zero =>
      have : exponent = 0 := by simpa using h
      simp [fastPow, this]
  | succ fuel ih =>
      have hhalf : exponent / 2 < 2^fuel := by
        rw [Nat.pow_succ] at h
        omega
      rw [fastPow, ih _ hhalf]
      split
      · rename_i heven
        have heq : exponent = exponent/2 + exponent/2 := by omega
        rw [← Nat.pow_add, ← heq]
      · rename_i hodd
        have hmod := Nat.mod_lt exponent (by decide : 0 < 2)
        have heq : exponent = (exponent/2 + exponent/2) + 1 := by omega
        rw [← Nat.pow_add, ← Nat.pow_succ]
        exact congrArg (fun e => a^e) (by omega)

theorem pow2_eq (exponent : Nat) (h : exponent < 2^32) :
    pow2 exponent = 2^exponent := fastPow_eq 2 32 exponent h

end SlhDsaSecurity.EligibilityCertificate

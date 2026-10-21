import SlhDsaSecurity.Proof.EligibilityCertificate.Arithmetic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace SlhDsaSecurity.EligibilityCertificate

open Finset Polynomial

private theorem ofDigits_ofFn (base size : Nat) (digits : Fin size → Nat) :
    Nat.ofDigits base (List.ofFn digits) = ∑ i, digits i * base^i.val := by
  induction size with
  | zero => simp
  | succ size ih =>
      rw [List.ofFn_succ, Nat.ofDigits_cons, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ac_rfl)

private theorem ofDigits_get (base : Nat) (hbase : 0 < base) (digits : List Nat)
    (hsmall : ∀ d ∈ digits, d < base) (i : Nat) (hi : i < digits.length) :
    Nat.ofDigits base digits / base^i % base = digits[i] := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i hbase digits hsmall,
    Nat.ofDigits_mod_eq_head!]
  have hhead : (digits.drop i).head! = digits[i] := by
    simp only [List.head!_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hi,
      Option.getD_some]
  rw [hhead, Nat.mod_eq_of_lt (hsmall _ (List.getElem_mem hi))]

/-- Base evaluation extracts a polynomial coefficient when no coefficient carries. -/
theorem coeff_eq_digit (p : ℕ[X]) (base : Nat) (hbase : 0 < base)
    (hsmall : ∀ i, p.coeff i < base) (i : Nat) :
    p.eval base / base^i % base = p.coeff i := by
  let size := max (p.natDegree + 1) (i + 1)
  have hdegree : p.natDegree < size := by dsimp [size]; omega
  have hi : i < size := by dsimp [size]; omega
  have heval : p.eval base = Nat.ofDigits base
      (List.ofFn (fun j : Fin size => p.coeff j.val)) := by
    rw [ofDigits_ofFn, p.eval_eq_sum_range' hdegree]
    exact (Fin.sum_univ_eq_sum_range _ size).symm
  rw [heval]
  have hget := ofDigits_get base hbase
    (List.ofFn (fun j : Fin size => p.coeff j.val))
    (by intro d hd; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd; exact hsmall j.val)
    i (by simpa using hi)
  exact hget.trans (List.getElem_ofFn _)

/-- Nonnegative coefficients are bounded by the evaluation at one. -/
theorem coeff_le_eval_one (p : ℕ[X]) (i : Nat) : p.coeff i ≤ p.eval 1 := by
  rw [p.eval_eq_sum_range' (n := max p.natDegree i + 1) (by omega)]
  simp only [one_pow, mul_one]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

end SlhDsaSecurity.EligibilityCertificate

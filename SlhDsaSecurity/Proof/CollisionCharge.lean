import SlhDsaSecurity.Proof.KeygenUniform

/-!
# The atomic charge for one structural fault witness

Every structural fault extracted from a forgery (a WOTS chain or compression collision,
a Merkle or FORS authentication-path collision, a FORS root compression, a WOTS chain
preimage, or a FORS leaf preimage) names one concrete oracle input whose answer must land
on a value fixed before that call. This file charges exactly that: a call whose byte input
is absent from the cache answers uniformly, so it hits any fixed target with probability
`2 ^ -128`, and lands in a fixed set of size `size` with probability at most
`size / 2 ^ 128`.

These are per-call charges in the shared oracle. Turning them into a bound on the whole
adaptive game additionally requires the verifier-counted accounting; no such bound is
claimed here.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.CollisionCharge

/-- A fresh tweakable call hits any value fixed before it with probability exactly `2 ^ -128`. -/
theorem fresh_tweakable_prob_hit (seed : Digest) (address : Address) (payload : Bytes)
    (target : Digest) (cache : QueryCache HashSpec)
    (hfresh : cache (Hashing.tweakableInput seed address payload) = none) :
    Pr[fun output => output = target |
      (simulateQ KeygenUniform.rom
        (Hashing.tweakable seed address payload : OracleComp OracleWorld Digest)).run' cache] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (KeygenUniform.fresh_tweakable_uniform seed address payload cache hfresh)]
  rw [probEvent_eq_eq_probOutput]
  simp [probOutput_uniformSample, Digest, n]

/-- A fresh tweakable call lands in a set fixed before it with probability at most
`size / 2 ^ 128`. This is the union bound over the honest values revealed so far. -/
theorem fresh_tweakable_prob_mem_le (seed : Digest) (address : Address) (payload : Bytes)
    (targets : Finset Digest) (cache : QueryCache HashSpec)
    (hfresh : cache (Hashing.tweakableInput seed address payload) = none) :
    Pr[fun output => output ∈ targets |
      (simulateQ KeygenUniform.rom
        (Hashing.tweakable seed address payload : OracleComp OracleWorld Digest)).run' cache] ≤
      targets.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (KeygenUniform.fresh_tweakable_uniform seed address payload cache hfresh)]
  rw [probEvent_eq_tsum_ite]
  have hpoint : ∀ value : Digest,
      Pr[= value | ($ᵗ Digest : ProbComp Digest)] = 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    intro value
    simp [probOutput_uniformSample, Digest, n]
  have hsum : ∑' value : Digest, (if value ∈ targets then
      Pr[= value | ($ᵗ Digest : ProbComp Digest)] else 0) =
      targets.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    calc ∑' value : Digest, (if value ∈ targets then
          Pr[= value | ($ᵗ Digest : ProbComp Digest)] else 0)
        = ∑' value : Digest, (if value ∈ targets then 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) else 0) :=
          tsum_congr fun value => by by_cases h : value ∈ targets <;> simp [h, hpoint]
      _ = targets.card * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
          rw [tsum_eq_sum (s := Finset.univ) (by simp)]
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      _ = targets.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
          simp [div_eq_mul_inv]
  rw [hsum]

end SlhDsaSecurity.CollisionCharge

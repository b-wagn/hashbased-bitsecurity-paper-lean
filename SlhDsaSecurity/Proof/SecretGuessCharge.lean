import SlhDsaSecurity.Proof.GrowthCharge

/-!
# The input-side charge: guessing a secret

Every other avenue is an event about a query's *answer*, and is charged by
`GrowthCharge.prob_badWithin_le`, whose hypothesis bounds the probability that a fresh uniform
answer is bad. Secret guessing is not of that shape: the randomness is the seed sampled at key
generation, and what matters is a query's *input*. So it needs its own charge, and this file
supplies it.

The essential statement is simple once the quantifiers are in the right order. A query input
of the secret-bearing format determines the secret it is guessing — the payload of
`PK.seed ‖ ADRS ‖ payload` is the guess — so a run that has queried a finite set of inputs has
staked at most that many guesses. Against a uniform `128`-bit secret drawn independently of
those inputs, the chance that any of them is right is at most `|inputs| / 2 ^ 128`, which at
`|inputs| ≤ q` is `q / 2 ^ 128 = 2q / 2 ^ 129`: exactly the input-side half of the target rate.

Two things are deliberately left as hypotheses rather than baked in.

* The guess extractor `guessOf` is arbitrary. For `SK.seed` it reads the payload of a
  tweakable input, for `SK.prf` the first field of a `PRF_msg` input; the bound does not care,
  which is why one lemma covers both secrets.
* The secret must be sampled *independently of the queried inputs*. In the experiment the seed
  is sampled first and the adversary sees the public key, so this independence is not
  immediate; supplying it is the deferred-sampling step, for which
  `CanonicalGraph.Programming.warmup_seed_uniform` — which exhibits the secret seed as an
  independent uniform cell of the presampled graph — is the intended route.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SecretGuessCharge

/-- A single input guesses the secret with probability `2 ^ -128`. -/
theorem prob_single_guess (guess : Digest) :
    Pr[fun secret : Digest => guess = secret | ($ᵗ Digest : ProbComp Digest)] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [show (fun secret : Digest => guess = secret) = (fun secret => secret = guess) from by
    funext secret; exact propext ⟨Eq.symm, Eq.symm⟩]
  rw [probEvent_eq_eq_probOutput]
  simp [probOutput_uniformSample, Digest, n]

open scoped Classical in
/-- **The input-side charge.** A run that has queried the inputs in `inputs` has staked at most
`inputs.card` guesses at the secret, so against an independently sampled uniform secret it
succeeds with probability at most `inputs.card / 2 ^ 128`. -/
theorem prob_secret_guessed_le (inputs : Finset Bytes) (guessOf : Bytes → Digest) :
    Pr[fun secret : Digest => ∃ input ∈ inputs, guessOf input = secret |
      ($ᵗ Digest : ProbComp Digest)] ≤
      inputs.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_exists_finset_le_sum inputs _ _) ?_
  calc ∑ input ∈ inputs,
        Pr[fun secret : Digest => guessOf input = secret |
          ($ᵗ Digest : ProbComp Digest)]
      = ∑ _input ∈ inputs, 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_congr rfl fun input _ => prob_single_guess (guessOf input)
    _ = inputs.card * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ inputs.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := le_of_eq (by rw [mul_one_div])

/-- Both secrets at once: a run staking `inputs.card` guesses at each of `SK.seed` and
`SK.prf` is charged `inputs.card / 2 ^ 128` for either, since a given input is read in only
one of the two formats and so guesses only one of them. -/
theorem prob_either_secret_guessed_le (inputs : Finset Bytes) (guessOf : Bytes → Digest)
    (isSeedFormat : Bytes → Prop) [DecidablePred isSeedFormat] :
    Pr[fun secret : Digest =>
        ∃ input ∈ inputs.filter isSeedFormat, guessOf input = secret |
      ($ᵗ Digest : ProbComp Digest)] ≤
      inputs.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prob_secret_guessed_le (inputs.filter isSeedFormat) guessOf) ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Finset.card_filter_le _ _)) _

/-! ## The form the coupling must deliver

`prob_secret_guessed_le` fixes the guessed inputs and then samples the secret. In the
experiment the seed is sampled first, so using it needs a step that moves the sampling to the
end — legitimate because, by `CanonicalGraph.Programming.warmup_seed_uniform`, the secret seed
is one coordinate of a uniform cell table, and every answer the adversary sees is an oracle
value that is uniform whatever the seed is. The statement below is the shape that step has to
produce: a run that yields the inputs it has queried, with the secret drawn afterwards.

Stating it this way keeps the obligation visible instead of hidden in a side condition. What
is *not* proved here is that the experiment can be rewritten in this order; that is the
until-first-hit coupling, whose abstract form is `BlindKey.hit_probability_le`. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- A run that has queried at most `limit` inputs guesses a secret drawn afterwards with
probability at most `limit / 2 ^ 128`. -/
theorem prob_run_guesses_secret_le {α : Type}
    (run : ProbComp (α × Finset Bytes)) (guessOf : Bytes → Digest) (limit : Nat)
    (hlimit : ∀ result ∈ support run, (result.2).card ≤ limit) :
    Pr[fun pair : (α × Finset Bytes) × Digest =>
        ∃ input ∈ pair.1.2, guessOf input = pair.2 |
      (do
        let result ← run
        let secret ← ($ᵗ Digest : ProbComp Digest)
        pure (result, secret))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc ∑' result, Pr[= result | run] *
        Pr[fun pair : (α × Finset Bytes) × Digest =>
            ∃ input ∈ pair.1.2, guessOf input = pair.2 |
          (do
            let secret ← ($ᵗ Digest : ProbComp Digest)
            pure (result, secret))]
      ≤ ∑' result, Pr[= result | run] * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun result => ?_
        by_cases hmem : result ∈ support run
        · refine mul_le_mul' le_rfl ?_
          rw [bind_pure_comp, probEvent_map]
          refine le_trans (prob_secret_guessed_le (result.2) guessOf) ?_
          exact ENNReal.div_le_div_right (Nat.cast_le.mpr (hlimit result hmem)) _
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          simp
    _ = (∑' result, Pr[= result | run]) * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

end SlhDsaSecurity.SecretGuessCharge

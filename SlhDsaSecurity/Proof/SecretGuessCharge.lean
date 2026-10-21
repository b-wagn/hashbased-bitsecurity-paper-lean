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

end SlhDsaSecurity.SecretGuessCharge

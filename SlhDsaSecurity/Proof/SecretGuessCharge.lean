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

/-! ## The form the coupling must deliver

`prob_secret_guessed_le` fixes the guessed inputs and then samples the secret. In the
experiment the seed is sampled first, so using it needs a step that moves the sampling to the
end — legitimate because, by `CanonicalGraph.Programming.warmup_seed_uniform`, the secret seed
is one coordinate of a uniform cell table, and every answer the adversary sees is an oracle
value that is uniform whatever the seed is. The statement below is the shape that step has to
produce: a run that yields the inputs it has queried, with the secret drawn afterwards.

Stating it this way keeps the obligation visible instead of hidden in a side condition. What
is *not* proved here is that the experiment can be rewritten in this order; that is the
until-first-hit coupling, whose abstract form is `BlindKey.hit_probability_le`.

**This duplicates existing machinery.** `BlindKey.mixture_hit_le_expected` already states the
same thing in the same shape — a transcript drawn first, a uniform key table drawn after, and
a bound of `expectedGuesses / 2 ^ 128` — for a whole table of keys rather than one `Digest`,
with `expectedGuesses_le_of_cap` supplying the pathwise cap. The lemma below is the `Finset`
specialisation and adds nothing beyond convenience; new work should use `BlindKey`.

That the two land on the same statement from opposite directions is the useful fact. Both are
the *blind* side of the coupling, and neither connects it to the real experiment, which
confirms that the gap is not in the key-guessing accounting — that is finished twice over —
but solely in the rewriting that makes the real transcript key-independent. -/

end SlhDsaSecurity.SecretGuessCharge

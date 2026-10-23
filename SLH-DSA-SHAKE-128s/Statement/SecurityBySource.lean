import «SLH-DSA-SHAKE-128s».Statement.Security
import Xmss.Statement.UnforgeabilityGame

/-!
# Counting hash calls by their source

This file states the experiment of `Security.lean` in the main development's framework,
`Xmss.SecurityGame`, where a game returns a
count **per kind of query** and a counting mode `Z` selects which kinds are work. The kinds are
`Xmss.Unforgeability.QueryKind`'s:

* `sign`: the adversary's signing requests, including repetitions and invalid contexts;
* `hash`: the adversary's own hash calls;
* `keygen`: key generation's hash calls;
* `signer`: the signer's hash calls, summed over all requests;
* `verifier`: final verification's hash calls.

Nothing about the experiment changes. `afterKeygen` is `experiment` after its first line, so
the game is key generation counted on its own, then the rest counted on its own: the adversary's
and the verifier's calls are the coordinates `experiment` already charges them to, and the
signer's are what is left of the rest.

SLH-DSA is a stateless scheme with a fixed parameter set, so the game is stated over `Unit`
schemes. FIPS 205 limits a key to `2 ^ 64` signatures, and the security of the parameter set is
only claimed below that limit; `Xmss.SecurityGame` has no such side condition, so
`HasLimitedSecurityBits` adds it, as an almost-sure bound on the `sign` count of the same game.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Security

/-- **The experiment after key generation**: the adversary's phase and the verifier, exactly as
`experiment` runs them. -/
noncomputable def afterKeygen (adversary : Adversary) (keys : SecretKey × PublicKey) :
    OracleComp OracleWorld Outcome := do
  let (sk, pk) := keys
  let ((forgery, adversaryCounts), signed) ←
    (simulateQ
      ((QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
          (fun input => Counts.single .hash (hashCost input)) + signingOracle sk)
      (adversary.main pk)).run.run []
  let (verified, verifierCounts) ← countQueries
    (fun input => Counts.single .verification (hashCost input))
    (Scheme.verify pk forgery.message forgery.signature)
  return {
    forgery := forgery
    signed := signed
    verified := verified
    counts := Multiplicative.toAdd adversaryCounts + verifierCounts }

/-- **The counts by source.** Key generation's hash calls and the rest's are counted apart; the
adversary's and the verifier's are the outcome's own coordinates, and the signer's are the rest
less those two. -/
def sourceCounts (outcome : Outcome) (keygenHashes laterHashes : Nat) :
    Xmss.Unforgeability.QueryCounts
  | .sign => outcome.counts .signing
  | .hash => outcome.counts .hash
  | .keygen => keygenHashes
  | .signer => laterHashes - outcome.counts .hash - outcome.counts .verification
  | .verifier => outcome.counts .verification

/-- **The experiment, counted by source.** -/
noncomputable def experimentBySource (adversary : Adversary) :
    OracleComp OracleWorld (Outcome × Xmss.Unforgeability.QueryCounts) := do
  let (keys, keygenHashes) ← countAllHashes Scheme.keygen
  let (outcome, laterHashes) ← countAllHashes (afterKeygen adversary keys)
  return (outcome, sourceCounts outcome keygenHashes laterHashes)

/-- All parties share one consistent oracle, initially empty. -/
noncomputable def runBySource (adversary : Adversary) :
    ProbComp (Outcome × Xmss.Unforgeability.QueryCounts) :=
  Xmss.RandomOracleModel.run (experimentBySource adversary)

instance (notion : Notion) (signed : SigningLog) (forgery : Forgery) :
    Decidable (Fresh notion signed forgery) := by
  cases notion <;> unfold Fresh <;> infer_instance

instance (notion : Notion) (outcome : Outcome) : Decidable (Wins notion outcome) := by
  unfold Wins
  infer_instance

/-- **The SLH-DSA game in the main development's framework.** -/
noncomputable def securityGame (notion : Notion) :
    Xmss.SecurityGame Unit Xmss.Unforgeability.QueryKind where
  Adversary := Adversary
  experiment := fun _ adversary =>
    (fun result => (decide (Wins notion result.1), result.2)) <$> runBySource adversary

/-- At most `2 ^ 64` signing requests, with probability one. -/
def WithinSigningLimit (notion : Notion) (adversary : Adversary) : Prop :=
  Pr[fun result => result.2 .sign ≤ signingLimit |
    (securityGame notion).experiment () adversary] = 1

/-- **`bits` bits of security in counting mode `Z`**, for every adversary within the signing
limit: `Xmss.SecurityGame.HasClassicalSecurityBits` with FIPS 205's limit added. -/
def HasLimitedSecurityBits (notion : Notion) (Z : Finset Xmss.Unforgeability.QueryKind)
    (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary, WithinSigningLimit notion adversary →
    (securityGame notion).HasQueryBound () Z adversary q →
    (securityGame notion).advantage () adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- **The adversary's own work**: its signing requests, its own hash calls, and the verification
of its forgery. The honest parties' hash calls — key generation's and the signer's — are free. -/
def adversaryWork : Finset Xmss.Unforgeability.QueryKind := {.sign, .hash, .verifier}

end SlhDsaSecurity.Security

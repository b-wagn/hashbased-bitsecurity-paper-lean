import SlhDsaSecurity.Proof.CacheAvailability
import SlhDsaSecurity.Proof.SecretGuessCharge
import SlhDsaSecurity.Proof.HashSeparation

/-!
# The gate the disclosed set opens, and what it costs

`CacheAvailability.signedAt` counts a digest as disclosing only when the cache also holds the
`PRF_msg` entry the signer would have made for that message. That closes the hole where an
adversary declares its own positions disclosed by querying a digest under a randomiser of its
own — but it opens a gate, because `Hashing.randomizerInput prf seed message` is
`prf ‖ seed ‖ message` and carries `SK.prf` in the clear. A run that queries there manufactures
the entry.

That query is a guess at `SK.prf` and is charged as one. `SecretGuessCharge` already bounds, at
one unit of `2 ^ -128` per queried input, the probability that a run meets a secret drawn after
it, and key generation's sampling supplies the deferral. `prfGuess` is the reading that makes
the instantiation go through: the seed a `PRF_msg` input carries, recovered from its first
block, which the format determines because `bytesBE n` is injective.

**The budget does not move, because the two events live on disjoint classes.** A canonical input
is `PK.seed ‖ address ‖ payload` and a `PRF_msg` input is `SK.prf ‖ PK.seed ‖ message`; their
first blocks are the two seeds, so unless the seeds coincide no input is both, and the two class
counts add to at most the record's size. The coincidence `SK.prf = PK.seed` is itself one unit
of `2 ^ -128`, which is one of the five the assembly's allowance already carries against a
margin of seven hundred and sixty.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomizerGate

open CanonicalGraph

/-! ## The seed a `PRF_msg` input carries -/

/-- **The first block of a `PRF_msg` input is its seed.** -/
theorem randomizerInput_prf_inj {prf prf' seed seed' : Digest} {message message' : Bytes}
    (hequal : Hashing.randomizerInput prf seed message =
      Hashing.randomizerInput prf' seed' message') : prf = prf' := by
  have hsplit : bytesBE n prf ++ (bytesBE n seed ++ message) =
      bytesBE n prf' ++ (bytesBE n seed' ++ message') := by
    simpa only [Hashing.randomizerInput, List.append_assoc] using hequal
  exact bytesBE_injective n (List.append_inj hsplit (by simp)).1

open scoped Classical in
/-- The seed a `PRF_msg` input carries in the clear, read off its first block. -/
noncomputable def prfGuess (input : Bytes) : Digest :=
  if hformat : ∃ (prf seed : Digest) (message : Bytes),
    input = Hashing.randomizerInput prf seed message then hformat.choose else default

theorem prfGuess_randomizerInput (prf seed : Digest) (message : Bytes) :
    prfGuess (Hashing.randomizerInput prf seed message) = prf := by
  classical
  have hformat : ∃ (candidate other : Digest) (payload : Bytes),
      Hashing.randomizerInput prf seed message =
        Hashing.randomizerInput candidate other payload := ⟨prf, seed, message, rfl⟩
  rw [prfGuess, dif_pos hformat]
  obtain ⟨other, payload, hspec⟩ := hformat.choose_spec
  exact (randomizerInput_prf_inj hspec).symm

/-! ## The charge -/

open scoped Classical in
/-- **The gate is paid for at one unit per query.** A run that has queried at most `limit`
inputs manufactures a `PRF_msg` entry at the real seed with probability at most
`limit / 2 ^ 128`, the seed being drawn after it. -/
theorem prob_run_randomizerInput_le {α : Type} (run : ProbComp (α × Finset Bytes))
    (limit : Nat) (hlimit : ∀ result ∈ support run, (result.2).card ≤ limit) :
    Pr[fun pair : (α × Finset Bytes) × Digest =>
        ∃ input ∈ pair.1.2, ∃ (seed : Digest) (message : Bytes),
          input = Hashing.randomizerInput pair.2 seed message |
      (do
        let result ← run
        let secret ← ($ᵗ Digest : ProbComp Digest)
        pure (result, secret))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (SecretGuessCharge.prob_run_guesses_secret_le run prfGuess limit hlimit)
  rintro ⟨result, secret⟩ - ⟨input, hinput, seed, message, rfl⟩
  exact ⟨_, hinput, prfGuess_randomizerInput secret seed message⟩

/-! ## The two classes do not meet -/

/-- **A canonical input is not a `PRF_msg` input**, the two seeds being distinct: their first
blocks are the seeds themselves. -/
theorem canonicalInput_ne_randomizerInput (publicSeed prfSeed seed : Digest) (cells : Cells)
    (parent : StructuralNode) (message : Bytes) (hne : prfSeed ≠ publicSeed) :
    canonicalInput publicSeed cells parent ≠ Hashing.randomizerInput prfSeed seed message :=
  fun hequal => HashSeparation.randomizer_tweakable_ne hne hequal.symm

open scoped Classical in
/-- **Each recorded input falls in at most one class**, so charging both events against the
record costs the record's size once, not twice. -/
theorem card_add_card_le (publicSeed prfSeed : Digest) (cells : Cells)
    (hne : prfSeed ≠ publicSeed) (record : Finset Bytes) :
    (record.filter fun input =>
        ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent).card +
      (record.filter fun input =>
        ∃ (seed : Digest) (message : Bytes),
          input = Hashing.randomizerInput prfSeed seed message).card ≤ record.card := by
  classical
  have hdisjoint : Disjoint
      (record.filter fun input =>
        ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent)
      (record.filter fun input =>
        ∃ (seed : Digest) (message : Bytes),
          input = Hashing.randomizerInput prfSeed seed message) := by
    rw [Finset.disjoint_left]
    intro input hcanonical hrandomizer
    obtain ⟨parent, hparent⟩ := (Finset.mem_filter.mp hcanonical).2
    obtain ⟨seed, message, hmessage⟩ := (Finset.mem_filter.mp hrandomizer).2
    exact canonicalInput_ne_randomizerInput publicSeed prfSeed seed cells parent message hne
      (hparent ▸ hmessage)
  rw [← Finset.card_union_of_disjoint hdisjoint]
  refine Finset.card_le_card ?_
  exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-! ## Where the separation stops

The gate's class is disjoint from the canonical one because the two formats open with different
seeds. It is **not** disjoint from the message class, and the reason is the shared oracle: a
message input *is* a `PRF_msg` input, at its own randomiser read as the seed and the public root
absorbed into the message. FIPS 205 separates `PRF_msg` from `H_msg` as functions; this model
idealises both as one oracle on byte strings, and only the first block distinguishes them.

So the signer's own digest query is a `PRF_msg` input at the real seed exactly when the
randomiser it derived for that message is the seed — an answer hitting a secret, which the
signer's queries can do once per request. -/

/-- **A message input is a `PRF_msg` input.** -/
theorem messageInput_eq_randomizerInput (randomizer : Digest) (pk : PublicKey)
    (message : Bytes) :
    Hashing.messageInput randomizer pk message =
      Hashing.randomizerInput randomizer pk.seed (bytesBE n pk.root ++ message) := by
  simp only [Hashing.messageInput, Hashing.randomizerInput, List.append_assoc]

/-- **And it is one at a given seed exactly when its randomiser is that seed.** -/
theorem messageInput_eq_randomizerInput_iff (randomizer prfSeed seed : Digest) (pk : PublicKey)
    (message payload : Bytes) :
    Hashing.messageInput randomizer pk message =
        Hashing.randomizerInput prfSeed seed payload →
      randomizer = prfSeed := by
  rw [messageInput_eq_randomizerInput]
  exact randomizerInput_prf_inj

/-- **The coincidence the disjointness excludes costs one unit.** -/
theorem prob_prf_eq_publicSeed (publicSeed : Digest) :
    Pr[fun prfSeed : Digest => prfSeed = publicSeed | ($ᵗ Digest : ProbComp Digest)] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [show (fun prfSeed : Digest => prfSeed = publicSeed) =
    (fun prfSeed : Digest => publicSeed = prfSeed) from by
      funext prfSeed; exact propext ⟨Eq.symm, Eq.symm⟩]
  exact SecretGuessCharge.prob_single_guess publicSeed

end SlhDsaSecurity.RandomizerGate

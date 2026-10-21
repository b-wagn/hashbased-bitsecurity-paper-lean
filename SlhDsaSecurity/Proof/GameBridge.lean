import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.VerifierNaturality
import SlhDsaSecurity.Proof.Correctness.Naturality
import SlhDsaSecurity.Proof.Extraction.HypertreeChain

/-!
# From the game's run to the extraction's `Id` statements

The extraction chain states everything with `(m := Id)` under the development's
`[HasQuery HashSpec Id]` variable; the game runs in `OracleComp`. Two facts bridge them, and
both already existed.

* `VerifierNaturality` and `Correctness.Naturality` give the naturality of every scheme
  operation: simulating it through any `impl` agreeing with the ambient `query` yields the same
  operation in the target monad. `CacheReplay.replay cache` agrees with
  `CacheReplay.replayQuery cache` by definition, so that hypothesis is `rfl`.
* `CacheReplay.run_eq_replay` says a hash-only run's result is what replaying it against its
  own final cache computes.

Composing them: whatever the game computed, the `Id`-level operation under `replayQuery` of the
final cache computed too. So an accepted forgery in the game *is* an accepted forgery in the
sense `HypertreeDispatch.cases_of_accepted` consumes, and the honest key the extraction compares
against is the one key generation actually produced.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.GameBridge

/-- The replay implementation agrees with the replay instance, by definition. -/
theorem replay_agrees (cache : QueryCache HashSpec) (input : Bytes) :
    CacheReplay.replay cache input =
      (@query _ HashSpec Id (CacheReplay.replayQuery cache) input : Id HashOutput) := rfl

/-- **What the game verified, the replayed verifier verifies.** -/
theorem verify_eq_replay (pk : PublicKey) (request : Message) (signature : Bytes)
    (initialCache finalCache : QueryCache HashSpec) (verified : Bool)
    (hmem : (verified, finalCache) ∈
      support ((simulateQ randomOracle
        (Scheme.verify (m := OracleComp HashSpec) pk request signature)).run initialCache)) :
    verified = @Scheme.verify Id Id.instMonad (CacheReplay.replayQuery finalCache) pk request signature := by
  rw [CacheReplay.run_eq_replay _ initialCache finalCache verified hmem]
  exact @VerifierNaturality.verify_simulate Id Id.instMonad _
    (CacheReplay.replay finalCache) (CacheReplay.replayQuery finalCache)
    (replay_agrees finalCache) pk request signature

/-- **What the game generated, the replayed key generation generates.** -/
theorem keygenInternal_eq_replay (secretSeed prfSeed publicSeed : Digest)
    (initialCache finalCache : QueryCache HashSpec) (keys : SecretKey × PublicKey)
    (hmem : (keys, finalCache) ∈
      support ((simulateQ randomOracle
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)).run
          initialCache)) :
    keys = @Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery finalCache)
      secretSeed prfSeed publicSeed := by
  rw [CacheReplay.run_eq_replay _ initialCache finalCache keys hmem]
  exact @Correctness.Naturality.keygenInternal_simulate Id Id.instMonad _
    (CacheReplay.replay finalCache) (CacheReplay.replayQuery finalCache)
    (replay_agrees finalCache) secretSeed prfSeed publicSeed

/-- The generated public key carries the public seed and the honest top root — the two
hypotheses `HypertreeDispatch.cases_of_accepted` takes. -/
theorem keygen_publicKey (secretSeed prfSeed publicSeed : Digest)
    (cache : QueryCache HashSpec) :
    (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed prfSeed publicSeed).2.seed = publicSeed ∧
      (@Scheme.keygenInternal Id Id.instMonad (CacheReplay.replayQuery cache)
        secretSeed prfSeed publicSeed).2.root =
        @SlhDsaSecurity.Extraction.HypertreeChain.honestNode (CacheReplay.replayQuery cache)
          secretSeed publicSeed (layers - 1) 0 :=
  ⟨rfl, rfl⟩

end SlhDsaSecurity.GameBridge

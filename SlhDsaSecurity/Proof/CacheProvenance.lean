import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.WarmedSplit
import SlhDsaSecurity.Proof.StrippedGame

/-!
# Where a cache entry came from

`CacheReplay.cached_of_queriesUnder` goes one way: an input a run consults is in the cache it
leaves. Provenance needs the other way, and it is the step only the game's structure gives —
**an entry that was not there before was made by a query**. A cache in this model is written
only by the oracle, so an entry the run ends with and did not start with is one its own handler
installed, and the input it installed it at is one the run consulted.

The two directions are not the same statement and neither implies the other. `replay` answers
`default` at an absent input, so a run can consult an input without the *replayed* evaluation
noticing, which is why the forward direction needs its own proof; and a cache can hold an entry
the run never asked at, if it was already there, which is why this direction needs the entry to
be fresh.

The proof is the same induction as `cache_value_persists`, read for its contrapositive at each
step: a query either is the probe — and then the head of the bind consults it — or is not, and
then the step leaves the probe absent, so the continuation must be the one that installed it.

The restriction to `OracleComp HashSpec` is the same one `CacheReplay` carries and for the same
reason, and it costs nothing here: every phase of the game that touches the cache other than
the adversary's own handler is a hash-only computation lifted into the game's world, and
`WarmedSplit.run_rom_liftM` routes its run back to `randomOracle` alone.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CacheProvenance

open Security CacheReplay

/-- **A hash-only run that ends holding an entry it did not start with consulted that input.** -/
theorem queriesUnder_of_fresh {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache computation probe := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact absurd hfresh hpresent
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases eq_or_ne probe input with rfl | hne
    · exact QueriesUnder.head probe next
    · have hstepfresh : step.2 probe = none := by
        rcases step_shape input initialCache step hstep with hshape | hshape
        · rw [hshape, QueryCache.cacheQuery_of_ne initialCache step.1 hne]
          exact hfresh
        · rw [hshape]
          exact hfresh
      have hfinal : finalCache input = some step.1 :=
        cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
          (step_cached input initialCache step hstep)
      refine QueriesUnder.tail input probe next ?_
      rw [show replay finalCache input = step.1 from by simp [replay, hfinal]]
      exact ih step.1 step.2 result hrest hstepfresh

/-- **The same, for a hash-only computation lifted into the game's world.** Key generation, the
signer and the verifier are all of this shape, so this is the form provenance uses on them. -/
theorem queriesUnder_of_fresh_liftM {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (liftM computation : OracleComp OracleWorld α)).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache computation probe := by
  rw [WarmedSplit.run_rom_liftM] at hmem
  exact queriesUnder_of_fresh computation initialCache finalCache result hmem probe hfresh
    hpresent

/-- The same again, for `OracleComp.liftComp`, which is the spelling `StrippedGame.sign_lift`
leaves the signer in. -/
theorem queriesUnder_of_fresh_liftComp {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (OracleComp.liftComp computation OracleWorld)).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache computation probe := by
  rw [StrippedGame.run_liftComp] at hmem
  exact queriesUnder_of_fresh computation initialCache finalCache result hmem probe hfresh
    hpresent

/-! ## The three honest phases, as the game spells them -/

/-- **A `PRF_msg` entry key generation installed is one key generation consulted.** -/
theorem queriesUnder_keygenInternal_of_fresh (secretSeed prfSeed publicSeed : Digest)
    (initialCache finalCache : QueryCache HashSpec) (keys : SecretKey × PublicKey)
    (hmem : (keys, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.keygenInternal secretSeed prfSeed publicSeed :
        OracleComp OracleWorld (SecretKey × PublicKey))).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed) probe := by
  rw [WarmedSplit.keygenInternal_liftM] at hmem
  exact queriesUnder_of_fresh_liftM _ initialCache finalCache keys hmem probe hfresh hpresent

/-- **An entry a signing request installed is one the signer consulted.** -/
theorem queriesUnder_sign_of_fresh (sk : SecretKey) (request : Message)
    (initialCache finalCache : QueryCache HashSpec) (answer : Option Bytes)
    (hmem : (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache (Scheme.sign (m := OracleComp HashSpec) sk request) probe := by
  rw [StrippedGame.sign_lift] at hmem
  exact queriesUnder_of_fresh_liftComp _ initialCache finalCache answer hmem probe hfresh hpresent

/-- **An entry verification installed is one the verifier consulted.** -/
theorem queriesUnder_verify_of_fresh (pk : PublicKey) (request : Message) (signature : Bytes)
    (initialCache finalCache : QueryCache HashSpec) (verified : Bool)
    (hmem : (verified, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.verify pk request signature : OracleComp OracleWorld Bool)).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder finalCache (Scheme.verify (m := OracleComp HashSpec) pk request signature)
      probe := by
  rw [WarmedSplit.verify_liftM] at hmem
  exact queriesUnder_of_fresh_liftM _ initialCache finalCache verified hmem probe hfresh hpresent

end SlhDsaSecurity.CacheProvenance

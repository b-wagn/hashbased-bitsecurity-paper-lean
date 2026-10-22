import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.SignerRandomiser

/-!
# A run that never asks inside a class cannot tell two caches apart outside it

The randomiser hop compares the game with one whose signer takes its randomiser from a side
table instead of from the oracle. The two differ in exactly one thing: the real game's cache
holds an entry at `Hashing.randomizerInput SK.prf PK.seed framed` for each served request, and
the blind game's does not. Everything the signer does *after* its randomiser therefore has to be
shown blind to that difference, and this file is that lemma.

The hypothesis is `SignerRandomiser.not_prfClass_of_probes_signInternalAt` in the shape an
induction over a run can carry, and the shape is the point. `HonestProbes.Probes` is relative to
a **replay cache**: it says what the computation asks when the cache answers everything. A run
does not — it draws fresh answers and installs them — so the probes of a run from `left` are the
probes under a cache *extending* `left`, namely the one the run itself ends with. Asking for the
property at every extension of the starting cache is what makes the induction close: at a fresh
query the cache grows by exactly that entry, and the hypothesis at the grown cache is the one the
continuation needs. Asked only at `left` it would be false at the first fresh query, and asked at
every cache whatsoever it would be a strictly stronger statement that
`HonestProbes`' lemmas do not give in that form.

`graft` is the correspondence between the two final caches: the blind run's cache is the real
run's with the class put back as the blind one had it. The conclusion is an equality of
*computations*, not of laws — the two runs draw the same values at the same points, because off
the class they agree on what is already cached.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.OffClassBlind

open CacheReplay StrippedGame

variable (S : Bytes → Prop) [DecidablePred S]

/-- One cache with another's `S`-part grafted on. -/
def graft (base cache : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => if S input then base input else cache input

variable {S}

/-- Two caches agreeing off `S` are each other's graft. -/
theorem graft_of_agree {left right : QueryCache HashSpec}
    (hagree : ∀ input, ¬ S input → left input = right input) : graft S right left = right := by
  funext input
  by_cases hmem : S input
  · rw [graft, if_pos hmem]
  · rw [graft, if_neg hmem]
    exact hagree input hmem

/-- Grafting an unchanged class part is unchanged. -/
theorem graft_cacheQuery_base {right : QueryCache HashSpec} {input : Bytes} (hinput : ¬ S input)
    (answer : HashOutput) (cache : QueryCache HashSpec) :
    graft S (right.cacheQuery input answer) cache = graft S right cache := by
  funext probe
  by_cases hmem : S probe
  · have hne : probe ≠ input := fun hequal => hinput (hequal ▸ hmem)
    rw [graft, if_pos hmem, graft, if_pos hmem, QueryCache.cacheQuery_of_ne right _ hne]
  · rw [graft, if_neg hmem, graft, if_neg hmem]

/-- Caching an answer off `S` keeps the agreement. -/
theorem agree_cacheQuery {left right : QueryCache HashSpec} {input : Bytes}
    (hagree : ∀ probe, ¬ S probe → left probe = right probe) (answer : HashOutput) :
    ∀ probe, ¬ S probe →
      (left.cacheQuery input answer) probe = (right.cacheQuery input answer) probe := by
  intro probe hprobe
  by_cases hequal : probe = input
  · subst hequal
    rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne left _ hequal, QueryCache.cacheQuery_of_ne right _ hequal]
    exact hagree probe hprobe

/-- **What the induction carries**: the computation asks nothing inside `S`, under every cache
that extends the one the run starts from. -/
def AsksOff (S : Bytes → Prop) (start : QueryCache HashSpec) {α : Type}
    (computation : OracleComp HashSpec α) : Prop :=
  ∀ cache, Extends start cache → ∀ probe, QueriesUnder cache computation probe → ¬ S probe

set_option maxHeartbeats 1000000 in
/-- **A run that never asks inside `S` cannot tell two caches agreeing off `S` apart.** Its run
from the one is its run from the other, with the `S`-part of the second grafted back on — an
equality of computations, since the two draw the same values at the same points. -/
theorem run_eq_graft {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (left right : QueryCache HashSpec),
      (∀ probe, ¬ S probe → left probe = right probe) → AsksOff S left computation →
        (simulateQ randomOracle computation).run right =
          (fun step : α × QueryCache HashSpec => (step.1, graft S right step.2)) <$>
            (simulateQ randomOracle computation).run left := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro left right hagree _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rw [graft_of_agree hagree]
  | query_bind input next ih =>
    intro left right hagree hasks
    have hinput : ¬ S input :=
      hasks left (Extends.refl left) input (QueriesUnder.head input next)
    have hquerySim : simulateQ randomOracle
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        randomOracle input := by simp
    have hstep : ∀ cache : QueryCache HashSpec,
        (simulateQ randomOracle
            (liftM (OracleSpec.query input) >>= next : OracleComp HashSpec α)).run cache =
          (randomOracle input).run cache >>= fun step =>
            (simulateQ randomOracle (next step.1)).run step.2 := by
      intro cache
      rw [simulateQ_bind, hquerySim, StateT.run_bind]
    rw [hstep right, hstep left]
    cases hcached : left input with
    | some value =>
      have hright : right input = some value := by rw [← hagree input hinput]; exact hcached
      have hrun : ∀ cache : QueryCache HashSpec, cache input = some value →
          (randomOracle input).run cache =
            (pure (value, cache) : ProbComp (HashOutput × QueryCache HashSpec)) := by
        intro cache hcache
        rw [QueryImpl.withCaching_run_some _ hcache]
      rw [hrun left hcached, hrun right hright, pure_bind, pure_bind]
      refine ih value left right hagree ?_
      intro cache hextends probe hprobe
      refine hasks cache hextends probe (QueriesUnder.tail input probe next ?_)
      rw [show replay cache input = value from by
        simp [replay, hextends input value hcached]]
      exact hprobe
    | none =>
      have hright : right input = none := by rw [← hagree input hinput]; exact hcached
      have hrun : ∀ cache : QueryCache HashSpec, cache input = none →
          (randomOracle input).run cache =
            (fun answer => (answer, cache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
        intro cache hcache
        rw [QueryImpl.withCaching_run_none _ hcache]
        simp [uniformSampleImpl]
      rw [hrun left hcached, hrun right hright, bind_map_left, bind_map_left, map_bind]
      refine bind_congr fun answer => ?_
      have hasksNext : AsksOff S (left.cacheQuery input answer) (next answer) := by
        intro cache hextends probe hprobe
        have hextendsLeft : Extends left cache := by
          intro probe' value hvalue
          refine hextends probe' value ?_
          have hne : probe' ≠ input := by
            intro hequal
            rw [hequal, hcached] at hvalue
            simp at hvalue
          rw [QueryCache.cacheQuery_of_ne left answer hne]
          exact hvalue
        refine hasks cache hextendsLeft probe (QueriesUnder.tail input probe next ?_)
        rw [show replay cache input = answer from by
          simp [replay,
            hextends input answer (QueryCache.cacheQuery_self left input answer)]]
        exact hprobe
      have hih := ih answer (left.cacheQuery input answer) (right.cacheQuery input answer)
        (agree_cacheQuery hagree answer) hasksNext
      rw [hih, show (fun step : α × QueryCache HashSpec =>
          (step.1, graft S (right.cacheQuery input answer) step.2)) =
          (fun step : α × QueryCache HashSpec => (step.1, graft S right step.2)) from by
        funext step
        rw [graft_cacheQuery_base hinput answer]]

/-! ## The signer, after its randomiser

The hypothesis `AsksOff` asks for is exactly
`SignerRandomiser.not_prfClass_of_probes_signInternalAt`, which is already stated at an arbitrary
cache — so it holds at every extension of the starting one without any further argument. -/

open scoped Classical in
/-- **The signer, after its randomiser, asks nothing inside the `PRF_msg` class at `SK.prf`** —
unless the randomiser it was handed is `SK.prf` itself. -/
theorem asksOff_signInternalAt (start : QueryCache HashSpec) (randomizer : Digest)
    (sk : SecretKey) (message : Bytes) {prfSeed : Digest}
    (hpublic : prfSeed ≠ sk.publicKey.seed) (hrandomizer : randomizer ≠ prfSeed) :
    AsksOff (RandomizerGate.PrfClass prfSeed) start
      (SignerRandomiser.signInternalAt (m := OracleComp HashSpec) randomizer sk message) :=
  fun cache _ probe hprobe =>
    SignerRandomiser.not_prfClass_of_probes_signInternalAt cache randomizer sk message hpublic
      hrandomizer probe hprobe

open scoped Classical in
/-- **So the rest of the signer is blind to the class the charge protects.** -/
theorem run_signInternalAt_eq_graft (left right : QueryCache HashSpec) (randomizer : Digest)
    (sk : SecretKey) (message : Bytes) {prfSeed : Digest}
    (hpublic : prfSeed ≠ sk.publicKey.seed) (hrandomizer : randomizer ≠ prfSeed)
    (hagree : ∀ probe, ¬ RandomizerGate.PrfClass prfSeed probe → left probe = right probe) :
    (simulateQ randomOracle
        (SignerRandomiser.signInternalAt (m := OracleComp HashSpec) randomizer sk message)).run
          right =
      (fun step : Signature × QueryCache HashSpec =>
          (step.1, graft (RandomizerGate.PrfClass prfSeed) right step.2)) <$>
        (simulateQ randomOracle
          (SignerRandomiser.signInternalAt (m := OracleComp HashSpec) randomizer sk message)).run
            left :=
  run_eq_graft _ left right hagree
    (asksOff_signInternalAt left randomizer sk message hpublic hrandomizer)

end SlhDsaSecurity.OffClassBlind

import SlhDsaSecurity.Proof.StrippedGame
import SlhDsaSecurity.Proof.WarmedSplit

/-!
# The charged work never exceeds the total hash count

The input half will charge the adversary's and the verifier's own queries, and the cap it needs
on how many there are has to come from `Security.HasTotalBudget` — which bounds
`Security.countAllHashes`, the total number of hash calls anywhere in the game. What the game's
own counters report is something else: `Outcome.counts.work` is the adversary's direct calls
plus the verifier's, charged inside the run rather than around it. This file proves the
inequality between them.

It is an inequality and not an equality, for two reasons, and both are the point of the
accounting rather than slack to be removed. Key generation and the signer hash without being
charged — that is what makes the honest phase free — and a signing *request* is charged on the
`.signing` counter, which `Counts.work` does not read. So `work` is a lower bound on the total,
never an upper one.

**No hypothesis is needed.** The worry that the signing charge might collide with the work
budget does not arise: `Counts.single .signing 1` has `work = 0`, so a request contributes
nothing to the side being bounded, while the signer's hash calls contribute to the side bounding
it. The two counters measure disjoint things and the comparison is unconditional.

The proof is three inductions joined by the phase split. The adversary's phase compares the
writer its handler accumulates against the calls the whole phase makes, where the signing
oracle's sub-runs are exactly the gap. The verifier's phase compares an outer `countQueries`
against the same total, and there the two agree. Key generation charges nothing at all.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.AdversaryQueries

open Security

/-! ## Charged work, as a number -/

theorem work_add (left right : Counts) :
    (left + right).work = left.work + right.work := by
  simp only [Counts.work, Pi.add_apply]
  omega

theorem work_single_hash (count : Nat) : (Counts.single .hash count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_verification (count : Nat) :
    (Counts.single .verification count).work = count := by
  simp [Counts.work, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem work_single_signing (count : Nat) : (Counts.single .signing count).work = 0 := by
  simp [Counts.work, Counts.single, Pi.single_eq_of_ne]

/-! ## Splitting a counted run, keeping both counts -/

theorem countAllHashes_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β) :
    countAllHashes (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> countAllHashes computation := by
  rw [map_eq_bind_pure_comp, GrowthBudget.countAllHashes_bind]
  simp only [Function.comp_def, GrowthBudget.countAllHashes_pure, pure_bind,
    map_eq_bind_pure_comp, Nat.add_zero]

/-- **A counted run factors at every sequencing point, with both counts kept.** The variant of
`WarmedSplit.mem_support_counted_bind` that remembers how the total splits. -/
theorem mem_support_counted_bind_count {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (result : (β × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (computation >>= next))).run cache)) :
    ∃ (value : α) (middleCache : QueryCache HashSpec) (first second : Nat),
      ((value, first), middleCache) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes computation)).run cache) ∧
      ((result.1.1, second), result.2) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes (next value))).run middleCache) ∧
      result.1.2 = first + second := by
  rw [GrowthBudget.countAllHashes_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨first, hfirst, hrest⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hpure⟩ := hrest
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  refine ⟨first.1.1, first.2, first.1.2, second.1.2, hfirst, ?_, by rw [hpure]⟩
  rw [show result.1.1 = second.1.1 from by rw [hpure],
    show result.2 = second.2 from by rw [hpure]]
  exact hsecond

/-! ## The adversary's own charges -/

/-- The adversary's own oracle: forward the query to the game's world and charge the hash. -/
noncomputable def adversaryImpl : QueryImpl OracleWorld CountedRun :=
  (QueryImpl.ofLift OracleWorld (StateT SigningLog (OracleComp OracleWorld))).withAddCost
    (fun input => Counts.single .hash (hashCost input))

/-- The adversary's own oracle, as the run it performs. -/
theorem run_adversaryImpl (queried : OracleWorld.Domain) (log : SigningLog) :
    ((WriterT.run (adversaryImpl queried)).run log) =
      (fun value =>
        ((value, Multiplicative.ofAdd (Counts.single .hash (hashCost queried))), log)) <$>
        (liftM (OracleWorld.query queried) : OracleComp OracleWorld (OracleWorld.Range queried)) := by
  simp only [adversaryImpl, QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply, WriterT.run_bind,
    AddWriterT.run_addTell, StateT.run_bind, StateT.run_pure, pure_bind,
    StrippedGame.run_liftM_state, StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def, mul_one]

/-! ## The verifier's charges -/

/-! ## The charged work of the whole game -/

/-! ## What the signer spends

A request whose context is too long is refused before any query; a request that is served is
charged **two** hashes — its randomiser's and its message digest's — and both calls are the
signer's, so the work budget never sees either. So every served request leaves two more units of
the total count unspent, on top of what key generation left; `two_le_count_sign` is that fact and
the statements below carry `2 * servedCount` because of it. The log says how many were served,
since the answer it records is `some` exactly when the frame was. -/

/-- The number of requests the signer served, read off the log it left. -/
def servedCount (log : SigningLog) : Nat :=
  (log.filter fun entry => entry.2.isSome).length

theorem servedCount_append (log : SigningLog) (request : Message) (answer : Option Bytes) :
    servedCount (log ++ [⟨request, answer⟩]) =
      servedCount log + (if answer.isSome then 1 else 0) := by
  rcases answer with _ | value <;> simp [servedCount]

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

attribute [local irreducible] WarmedGame.afterSeeds

end SlhDsaSecurity.AdversaryQueries

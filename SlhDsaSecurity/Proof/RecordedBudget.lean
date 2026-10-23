import SlhDsaSecurity.Proof.RecordedQueries
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.HonestGrowth
import SlhDsaSecurity.Proof.GraphStakes
import SlhDsaSecurity.Proof.ClaimedProbes

/-!
# The budget, carried to the recorded game

`RecordedQueries.card_toFinset_le` bounds the recorded set by whatever bound is available on the
work this run charges. `Security.HasTotalBudget` is such a bound, but it speaks about
`Security.runAll` — the unwarmed, unstripped, uninstrumented game. This file carries it across
the three steps that separate them.

Each step is a transfer of an almost-sure property across equal laws, and none of them touches
the counters: warming changes the cache and not the outcome, stripping changes what the honest
phase asks and not what the outcome reports, and the recording is invisible. That the `Outcome`
survives all three unchanged is exactly why the work budget — rather than the total hash count,
which stripping does lower — is the quantity to carry.

The one small gap to bridge is that `WarmedGame.tail` is counted while the stripped and recorded
games are not. `map_countAllHashes` closes it: the counter only decorates the value, so
forgetting it returns the computation itself, and a supported uncounted run therefore has a
supported counted counterpart.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedBudget

open Security WarmedGame

/-- **Forgetting the count returns the computation.** -/
theorem map_countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countAllHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [GrowthBudget.countAllHashes_pure, map_pure]
  | query_bind queried next ih =>
    rw [GrowthBudget.countAllHashes_query_bind, map_bind]
    exact congrArg (Bind.bind _) (funext fun answer => by
      rw [Functor.map_map]
      exact ih answer)

attribute [local irreducible] WarmedGame.afterSeeds StrippedGame.strippedAfterSeeds
  RecordedQueries.recordedAfterSeeds Scheme.verify Scheme.keygenInternal Security.countQueries

/-! ## Reserving what key generation spent

Key generation's hash calls are charged to the budget and counted in neither `.hash` nor
`.verification`, so the work the game charges leaves that much of the budget unspent. Reserving
it rather than discarding it is what pays for the forgery's own claimed cells: the input half
records one candidate per claimed cell, a constant `GraphStakes.claimedCount = 259` of them,
against the `2 ^ subtreeHeight = 512` key generation puts back. -/

/-! ## Reserving what the signer spent

Key generation's spend is a constant, and a defect proportional to the number of served
requests cannot be paid out of a constant. The signer's own hashing is the room that grows with
them: a served request is charged at least **two** hashes — its randomiser's and its message
digest's — and both calls are the signer's, so the work budget never sees either. That is
`AdversaryQueries.two_le_count_sign`, and it is why the statements below reserve
`2 * servedCount` rather than one unit apiece. -/

end SlhDsaSecurity.RecordedBudget

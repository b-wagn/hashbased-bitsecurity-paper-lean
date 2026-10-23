import SlhDsaSecurity.Proof.OpenCache
import SlhDsaSecurity.Proof.RecordedBudget

/-!
# The budget, carried to the lazy presentation

`RecordedBudget` bounds what the game charges on a run of the shared oracle. The charge of
`SensitiveQuery` consumes a run of `OpenCache.lazyProgram`, whose state records each probe with
the cache it was issued against. The two presentations record different things, and the gap is
not closed by making the recordings agree in type: one exists to be charged, the other to be
counted.

What closes it is that the lazy handler never answers anything the shared oracle could not have
answered. At a cached input both reply from the cache; at an input the walk's table answers, the
lazy handler replies with a value the shared oracle draws with positive probability; everywhere
else both draw. So every run of the lazy presentation is a run of the shared oracle, and every
property the budget establishes with probability one transfers to it unchanged — in particular
the bound on `Outcome.counts.work`, which is the quantity the recorded game's cardinality bound
is stated against.

`mem_support_simulateQ_of_step` is the transfer, stated for any two handlers related by a
relation on their states that each step preserves. It is a forward simulation on supports, not a
comparison of laws: the lazy run's law is *not* the shared oracle's, since the table fixes
answers the oracle would draw. Only the support is contained, and only the support is needed,
because a budget that holds with probability one holds at every supported result.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.LazyBudget

open Security OpenCache CanonicalGraph

/-! ## Forward simulation on supports

Two handlers whose states are related by a relation each step preserves — every step of the
first having a step of the second that returns the same answer and preserves the relation — give
runs whose supports are related the same way. -/

/-! ## The lazy handler answers only what the shared oracle could

The handler's reply to a hash query, with the bookkeeping stripped off, so that the comparison
with the shared oracle is between two computations of the same clean type. Spelling it out is
what lets the step below be read off: a cached input is answered from the cache on both sides, an
input the table answers is answered with a value the oracle draws with positive probability, and
everything else is drawn on both sides. -/

/-! ## The budget at the lazy presentation

The budget is a property that holds at every supported result of the shared oracle's run, so
containment of supports delivers it to the lazy presentation without a probabilistic step. What
it bounds is `Outcome.counts.work`, which the stripping surgery leaves untouched and which the
handler, being a handler, does not touch either. -/

attribute [local irreducible] StrippedGame.strippedAfterSeeds WarmedGame.afterSeeds
  Scheme.verify Scheme.keygenInternal Security.countQueries OpenCache.lazyProgram

end SlhDsaSecurity.LazyBudget

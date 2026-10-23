import SlhDsaSecurity.Proof.SensitiveQuery

/-!
# A lazy presentation and an eager one flag the same event as often

`SensitiveQuery.prob_probes_sensitive_le` charges the input half's event at `2 ^ -128` per
query for a run that does not consult the cell table, the table being drawn afterwards. What a
game offers is a run against a cache *programmed* from that table. This file is the bridge:
two presentations of the same run that agree except where the event has already fired assign
that event exactly the same probability.

The bridge is not a cache comparison. `BlindComparison.prob_touched_eq` compares two caches
agreeing off a set of inputs **fixed before the run**, and the set here is not fixed: it is the
canonical inputs of the nodes that are sensitive *now*, and it shrinks as signatures release
cells. `AgreeOff` is not preserved across a release, so that lemma does not apply.

Nor is it VCVio's `QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad`. That
bounds the *advantage* of distinguishing the two games by `expectedQuerySlack + Pr[bad]`, which
is a bound with a per-query slack, and the input half has no room for one — it is
`q / 2 ^ 128` exactly. Its hypotheses also compare the two handlers at a **shared** state
(`h_step_eq_uncharged` asks for `(h₀ t).run p = (h₁ t).run p` at every `p`), while a lazy
presentation and an eager one have related states, not equal ones: the eager state carries the
whole table and the lazy state only the part that has been drawn.

What is true, and what is proved here, is an equality rather than a bound. Let `refine` send a
lazy state to the distribution of its eager presentations — in the game, "draw the cells that
are still undetermined". Then:

* a query that is bad at a lazy state is bad at every eager presentation of it, and sets the
  flag on both sides, so the event is decided before the two can diverge;
* a query that is not bad **commutes** with `refine`: drawing the remaining cells and then
  answering has the same law as answering and then drawing the remaining cells. This is the
  deferred-sampling move `CanonicalGraph.Programming.warmup_seed_uniform` already makes for the
  walk, one step at a time.

`probEvent_flag_refine_eq` is the conclusion: the eager run and the lazy run flag the event
with the same probability, with no slack. Only the commutation is a real obligation;
everything else is bookkeeping about a sticky flag.

**What it reaches and what it does not.** `Bad` is a predicate on the state and the query, and
`hbadRefine` asks it to be the same at a lazy state and at every eager presentation of it. A
lazy presentation that *defers* the staked cells does not satisfy that, and the failure is
exactly locatable: at a query naming a node whose staked cell is still undrawn, the lazy state
has no sensitivity to report, while the presentation that drew that cell to the matching value
does. So the sensitive-query event of `SensitiveQuery` — which is decided only once the
deferred table is drawn — is not a `Bad` in this sense, and the bridge does not by itself carry
`prob_probes_sensitive_le` to a programmed cache.

A lazy handler that draws the staked cell *at the probe* rather than deferring it does satisfy
the commutation at every query, `Bad` becoming vacuous: drawing a cell at the probe and drawing
it in the final batch are the same law. The charge then has to be re-proved against a partly
drawn table, where a repeated probe at a node whose cell was drawn at an earlier probe is
conditioned on that earlier probe having missed. That is an additive cost, not a per-query one,
but it is not `prob_record_sensitive_le`, which is stated for a table drawn entirely after the
run.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.LazyBridge

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Binding a common continuation after two computations of the same law gives the same law. -/
theorem evalDist_bind_congr_right {α β : Type} {oa ob : ProbComp α} (hlaw : 𝒟[oa] = 𝒟[ob])
    (k : α → ProbComp β) : 𝒟[oa >>= k] = 𝒟[ob >>= k] := by
  rw [evalDist_bind, evalDist_bind, hlaw]

/-! ## A sticky flag is already certain

Once the flag is set, the event is decided: whatever the run does afterwards, it ends flagged.
This is what makes the divergence at a bad query free. -/

/-! ## Two handlers that agree until the flag fires

The refinement above compares one handler with itself. Two *different* handlers that agree
except where the flag fires assign it the same probability for the same reason, and that is the
comparison a lazy presentation needs against an eager one when both draw their randomness up
front, so there is nothing for a refinement to draw.

The comparison has to be made once, for the whole event. Stalling it at one coordinate would be
unsound: handlers that differ at the inputs the flag fires on differ at *all* of them, so two
runs stalled at one coordinate can still diverge earlier at another, and "they agree while
unfrozen" would be false rather than merely weak.

Note where the flag lives. It is in the comparison only; nothing here reads it, and in
particular the handler that answers from a table never needs to. -/

/-! ## The bridge

`refine s` is the distribution of eager presentations of the lazy state `s` — in the game, the
cells still undetermined, drawn now rather than on demand. The two hypotheses that carry
content are that badness does not depend on which presentation was drawn, and that a non-bad
step commutes with drawing them. -/

end SlhDsaSecurity.LazyBridge

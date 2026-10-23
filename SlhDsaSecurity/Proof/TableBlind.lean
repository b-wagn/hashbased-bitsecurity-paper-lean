import SlhDsaSecurity.Proof.SensitiveQuery
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# A run that reads only part of the table is blind to the rest

`DrawnTable` settles the rate: a prober meets the cell table at one unit of `2 ^ -128` per
probe, whether the cells are drawn before the run, during it, or after, because feedback that
is constant until the event conveys nothing. What that charge still asks of a presentation is
that the probes it records be produced without reading the cells it is charged against.

This file supplies the lifting that turns a *per-step* statement of that into a run-level one.
A handler is parameterised by the table it may read; `evalDist_run_congr_of_step` says that if
each step's law is unchanged by altering the table within an equivalence `Agree`, so is the
whole run's, hence so is any event about its record. The per-step hypothesis is where the
graph enters: a query at a node all of whose children's cells are available is answered by that
node's own cell, which `CanonicalGraph.available_of_children_available` says is available too,
so the answer is a function of the available cells alone and of nothing else.

`prob_blind_run_sensitive_le` is the composition when the two parts of the table are given
separately: a run that reads an independently drawn table of available cells, and records its
probes, meets the *sensitive* cells at one unit per probe.

**What this settles and what it does not.** It settles the clauses whose unavailable cells are
fixed before the run: the WOTS `PRF` cells and the WOTS chain values below the revealed digit,
the digit being a function of the key and the seeds because each hypertree key signs exactly one
message.

*Not* because a `PRF` cell is never disclosed — `SensitiveShape.Available` says a WOTS `PRF`
cell is available exactly when `revealed key chain = 0`, and a FORS `PRF` cell exactly when its
index is signed, so both are disclosed on the nose in those cases. The property the clause needs
is the weaker and true one: **whether such a cell is disclosed is decided before the run**, which
holds for WOTS because `revealed` is a function of the key and the seeds. It does not hold for
FORS, whose signed set the adversary chooses, and the FORS case is separately excluded below. There the available part is determined by the
walk, the run reads only it, and the charge applies to the rest for the whole run.

It applies to a presentation in which the handler reads the table, which is the lazy one. In a
presentation where the table enters through the *initial cache* instead — the programmed cache
of the walk — the dependence is in the state rather than in the handler, and the lifting below
says nothing: two caches built from tables that differ are told apart by a single query at a
canonical input where they differ, so no run-level congruence holds. That difference is the
whole reason the lazy presentation is worth having.

It does not settle the FORS clause. There the set of unavailable cells shrinks as signatures
are issued, so "the part the run reads" is not fixed: a FORS secret is unavailable when an
earlier probe is made and available when a later one is, and a run that reads it after the
release is not blind to it. The charge only needs the probe at step `k` to be independent of
the cells unavailable *at step `k`*, which is true and is weaker than blindness for the whole
run — but it is a statement about prefixes, and the lifting below is not indexed by them.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TableBlind

open SensitiveQuery

/-! ## Lifting blindness from a step to a run -/

/-- Two computations of the same law with continuations of the same law bind to the same law. -/
theorem evalDist_bind_congr {α β : Type} {oa ob : ProbComp α} {f g : α → ProbComp β}
    (hlaw : 𝒟[oa] = 𝒟[ob]) (hcont : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[ob >>= g] := by
  rw [evalDist_bind, evalDist_bind, hlaw]
  exact congrArg _ (funext hcont)

/-- **Blindness lifts from a step to a run.** If altering the table within `Agree` leaves every
step's law alone, it leaves the whole run's law alone. -/
theorem evalDist_run_congr_of_step {ι : Type} {spec : OracleSpec ι} {σ Table : Type}
    (impl : Table → QueryImpl spec (StateT σ ProbComp)) (Agree : Table → Table → Prop)
    (hstep : ∀ (t : spec.Domain) (s : σ) (left right : Table), Agree left right →
      𝒟[(impl left t).run s] = 𝒟[(impl right t).run s])
    {γ : Type} (oa : OracleComp spec γ) (left right : Table) (hagree : Agree left right)
    (s : σ) :
    𝒟[(simulateQ (impl left) oa).run s] = 𝒟[(simulateQ (impl right) oa).run s] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact evalDist_bind_congr (hstep t s left right hagree) fun p => ih p.1 p.2

/-! ## The charge against a run that reads only the available cells

When the two parts of the table are given separately there is nothing to lift: the run is a
computation in which the sensitive cells do not occur, so they may be drawn after it. -/

variable {Node Index State : Type} [Fintype Index] [DecidableEq Index]

end SlhDsaSecurity.TableBlind

import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# The classical random-oracle model

The oracle world shared by all parties of a security experiment, and its semantics: private
uniform sampling, and a hash oracle `Input →ₒ Output` implemented as a lazily sampled, consistent
random oracle. `run` runs a computation of this world from an empty oracle cache. `hashCost` is
the cost of a query of the world: one unit per hash call (also for a repeated input), nothing per
uniform sample; it is the unit in which security notions count hash calls.
-/

open OracleComp OracleSpec

namespace XmssSecurity.RandomOracleModel

variable (Input Output : Type) [DecidableEq Input] [SampleableType Output]

/-- The hash oracle `H : Input → Output`. -/
abbrev HashSpec : OracleSpec Input := Input →ₒ Output

/-- Private uniform sampling and the shared hash oracle. -/
abbrev World := unifSpec + HashSpec Input Output

/-- Forward uniform sampling; answer a fresh hash input by a uniform output and cache it, and a
repeated input from the cache. -/
noncomputable def impl :
    QueryImpl (World Input Output) (StateT (QueryCache (HashSpec Input Output)) ProbComp) :=
  unifFwdImpl (HashSpec Input Output) +
    (randomOracle : QueryImpl (HashSpec Input Output)
      (StateT (QueryCache (HashSpec Input Output)) ProbComp))

/-- One unit per hash call, including repeated inputs; nothing per uniform sample. -/
def hashCost : (World Input Output).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

variable {Input Output}

/-- Run a computation of the random-oracle world from an empty cache. -/
noncomputable def run {α : Type} (computation : OracleComp (World Input Output) α) :
    ProbComp α :=
  (simulateQ (impl Input Output) computation).run' ∅

end XmssSecurity.RandomOracleModel

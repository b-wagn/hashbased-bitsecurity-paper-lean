import SlhDsaSecurity.Proof.GraphStakes
import SlhDsaSecurity.Proof.HonestProbes

/-!
# A sensitive candidate is a canonical input

The charge is handed the probes at inputs the walk's table answers, not every probe the run
makes. That filter is what keeps the stripped honest phase out of the count: it still asks
about the message digest and its randomiser, inputs no table of graph cells can hold, and a
run may make `signingLimit = 2 ^ 64` signing requests. Charged against the raw probe list the
input half would come in at `2 ^ -64` and be gone.

Nothing is lost by filtering, and this is the reason. A sensitive candidate is the canonical
input of its node — whatever value the staked cell happens to take — and the walk programmed
an entry at every canonical input. So the filter drops only probes the charge could never have
fired on.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.SensitiveWarm

open CanonicalGraph GraphStakes

variable (publicSeed : Digest) {State : Type}

/-- **A sensitive candidate is a canonical input.** -/
theorem canonical_of_sensitive {unavailable : State → Node → Prop} (table : Cells)
    (state : State) {candidate : Bytes}
    (hsensitive : SensitiveQuery.Sensitive (stakes publicSeed) unavailable table state candidate) :
    HonestProbes.Canonical publicSeed table candidate := by
  obtain ⟨node, -, hinput⟩ := hsensitive
  exact ⟨node.parent, hinput.symm.trans (inputOf_eq_canonicalInput publicSeed node table)⟩

/-- **So the walk's table answers it**, which is the hypothesis the filtered record's bound
takes. -/
theorem warmCache_ne_none_of_sensitive {unavailable : State → Node → Prop}
    (secretSeed : Digest) (outputs : CanonicalGraph.Programming.Outputs) (state : State)
    {candidate : Bytes}
    (hsensitive : SensitiveQuery.Sensitive (stakes publicSeed) unavailable
      (HonestProbes.replayCells (HonestProbes.warmCache publicSeed secretSeed outputs)
        secretSeed publicSeed) state candidate) :
    HonestProbes.warmCache publicSeed secretSeed outputs candidate ≠ none :=
  HonestProbes.warmCache_ne_none publicSeed secretSeed outputs candidate
    (canonical_of_sensitive publicSeed _ state hsensitive)

end SlhDsaSecurity.SensitiveWarm

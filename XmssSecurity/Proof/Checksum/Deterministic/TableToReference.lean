import XmssSecurity.Proof.Checksum.Deterministic.RequestSampling
import XmssSecurity.Proof.Checksum.Deterministic.ReferenceSource
import XmssSecurity.Proof.Checksum.Deterministic.MemoTable
import XmssSecurity.Proof.Checksum.Deterministic.CostState

open OracleComp OracleSpec

namespace XmssSecurity.Checksum.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableSign

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : ChainSecrets) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (worldHandler hash) (gameAfterSecrets (memoAdversary adversary)
        parameter outputs)).run state] := by
  unfold tableGameAfterSecrets gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  have hleft (randomizers) := runSigning_sourceGame randomizers (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    ⟨result.1.1, parameter⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    (sourceGame ⟨result.1.1, parameter⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

end XmssSecurity.Checksum.Seeded

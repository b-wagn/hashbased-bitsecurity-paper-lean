import XmssSecurity.Proof.Checksum.Seeded.BudgetTransfer
import XmssSecurity.Proof.Checksum.Deterministic.GameExpansion

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev SigningMaterial := HashOutput × ChainOutputs × RandomizerOutputs

noncomputable def drawSigningMaterial : ProbComp SigningMaterial := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← ($ᵗ ChainOutputs)
  let randomizers ← sampleRandomizerOutputs
  return (parameterOutput, outputs, randomizers)

noncomputable def independentTableGame (adversary : Adversary) : ProbComp Bool := do
  let material ← drawSigningMaterial
  (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run' ∅

theorem evalDist_programmedDeterministicGame_seed_last (adversary : Adversary) :
    𝒟[programmedDeterministicGame adversary] = 𝒟[do
      let material ← drawSigningMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] := by
  have heq : programmedDeterministicGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawSigningMaterial
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)) := by
    simp only [programmedDeterministicGame, drawSigningMaterial, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

end XmssSecurity.Checksum.Seeded

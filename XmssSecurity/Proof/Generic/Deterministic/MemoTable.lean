import XmssSecurity.Proof.Generic.Deterministic.MemoGame
import XmssSecurity.Proof.Generic.Deterministic.GameComparison

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false

theorem prob_tableGameAfterSecrets_le_memo (adversary : Adversary) (parameter : PublicParameter)
    (outputs : ChainSecrets) (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ romImpl (tableGameAfterSecrets adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ romImpl (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterSecrets
  rw [run'_lift_hash_bind, run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem prob_independentTableGame_le_memo (adversary : Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterSecrets_le_memo _ _ _ _ ∅

end XmssSecurity.Generic.Seeded

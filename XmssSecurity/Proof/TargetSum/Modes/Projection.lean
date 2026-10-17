import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Common.Modes.Direct
import XmssSecurity.Proof.TargetSum.Direct.Bridge

/-!
# The counted game projects to the game

In every counting mode, forgetting the charge of `SUFCMA.gameCounted` gives `SUFCMA.game`: the
accounting never changes what the experiment does.
-/

open OracleComp OracleSpec

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

theorem map_fst_gameCounted [DecidableEq Msg] [DecidableEq Sig] (mode : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) :
    Prod.fst <$> gameCounted mode cost scheme adversary = game scheme adversary := by
  have h : ∀ m : CountingMode, Prod.fst <$> gameCounted m cost scheme adversary =
      Prod.fst <$> gameDetailed cost scheme adversary := fun m => by
    rw [gameCounted_eq_map_gameDetailed, Functor.map_map]
  rw [h mode, ← h CountingMode.direct, gameCounted_direct_eq]
  exact Security.gameCounted_map_fst cost scheme adversary

end XmssSecurity.TargetSum.Modes

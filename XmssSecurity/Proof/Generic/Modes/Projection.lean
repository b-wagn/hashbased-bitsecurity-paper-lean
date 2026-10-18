import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Common.Modes.Direct
import XmssSecurity.Proof.Generic.Direct.Bridge

/-!
# The counted game projects to the game

In every counting mode, forgetting the charge of `SUFCMA.gameCounted` gives `SUFCMA.game`: the
accounting never changes what the experiment does.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Modes

variable [Code]

open XmssSecurity.Modes

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

end XmssSecurity.Generic.Modes

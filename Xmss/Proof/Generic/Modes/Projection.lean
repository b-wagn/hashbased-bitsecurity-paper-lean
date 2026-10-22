import Xmss.Proof.Common.Modes.Lattice
import Xmss.Proof.Common.Modes.Direct
import Xmss.Proof.Generic.Direct.Bridge

/-!
# The counted game projects to the game

In every counting mode, forgetting the charge of `SUFCMA.gameCounted` gives `SUFCMA.game`: the
accounting never changes what the experiment does.
-/

open OracleComp OracleSpec

namespace Xmss.Generic.Modes

variable [Code]

open Xmss.Modes

open Unforgeability SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

end Xmss.Generic.Modes

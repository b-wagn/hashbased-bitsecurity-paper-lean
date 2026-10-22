import Xmss.Proof.Generic.ConsistentQueryBound
import Xmss.Proof.Generic.Scheme.Xmss
import Xmss.Proof.Common.Adversary.LegacyNotions
import Xmss.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# From the statement to the proof's game

The SUF-CMA game for `xmss` (`SUFCMA.game xmss`) and the proof's internal game for the seeded
scheme (`gameCore Seeded.scheme`) are the same computation, so success probabilities and
hash-query counts transfer exactly.
-/

open OracleComp OracleSpec ENNReal
namespace Xmss.Generic.AdversaryBridge

variable [Code]

set_option backward.isDefEq.respectTransparency false

/-- The statement's adversary type and the proof's are the same. -/
abbrev StatementAdversary := Unforgeability.Adversary OracleWorld PublicKey Message Signature lifetime

def embed (adversary : StatementAdversary) : Xmss.Generic.Adversary :=
  ⟨adversary.main⟩

theorem game_embed (adversary : StatementAdversary) :
    Xmss.Generic.gameCore Seeded.scheme (embed adversary) = SUFCMA.game xmss adversary := by
  unfold Xmss.Generic.gameCore Seeded.gameRest SUFCMA.game
  rfl

end Xmss.Generic.AdversaryBridge

import XmssSecurity.Proof.Generic.ConsistentQueryBound
import XmssSecurity.Proof.Generic.Scheme.Xmss
import XmssSecurity.Proof.Common.Adversary.LegacyNotions
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# From the statement to the proof's game

The statement's SUF-CMA experiment for `xmss` (`SUFCMA.notionTotal xmss`) and the proof's internal
game for the seeded scheme (`gameCore Seeded.scheme`) are the same computation, so success
probabilities and hash-query counts transfer exactly.
-/

open OracleComp OracleSpec ENNReal
namespace XmssSecurity.Generic.Security

variable [Code]

set_option backward.isDefEq.respectTransparency false

/-- The statement's adversary type and the proof's are the same. -/
abbrev StatementAdversary := SUFCMA.Adversary OracleWorld PublicKey Message Signature lifetime

def embed (adversary : StatementAdversary) : XmssSecurity.Generic.Adversary :=
  ⟨adversary.main⟩

theorem game_embed (adversary : StatementAdversary) :
    XmssSecurity.Generic.gameCore Seeded.scheme (embed adversary) = SUFCMA.game xmss adversary := by
  unfold XmssSecurity.Generic.gameCore Seeded.gameRest SUFCMA.game
  rfl

end XmssSecurity.Generic.Security

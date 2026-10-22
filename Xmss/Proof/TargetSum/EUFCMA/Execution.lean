import Xmss.Proof.TargetSum.EUFCMA.Projection
import Xmss.Proof.Common.EUFCMA.Reduction
import Xmss.Proof.Generic.DetailedExecution
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Standard freshness on the existing proof execution. The reference scheme's
cache and trace constructions can be reused without changing their executions. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

noncomputable def gameRest {Key : Type} (scheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (Unforgeability.SigningTranscript.Valid log ∧
    ¬Unforgeability.SigningTranscript.ContainsRequest log forgery) && verified

noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  gameRest scheme adversary pk sk

noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key)
    (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

def standardWon (outcome : GameOutcome) : Bool :=
  decide (Unforgeability.SigningTranscript.Valid outcome.signingLog ∧
    ¬Unforgeability.SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery) && outcome.verified

theorem standardWon_eq_true_iff (outcome : GameOutcome) :
    standardWon outcome = true ↔ Unforgeability.SigningTranscript.Valid outcome.signingLog ∧
      ¬Unforgeability.SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery ∧ outcome.verified = true := by
  simp [standardWon, and_assoc]

theorem strongWon_of_standardWon (outcome : GameOutcome) (hwin : standardWon outcome = true) :
    outcome.won = true := by
  rw [standardWon_eq_true_iff] at hwin
  rw [GameOutcome.won_eq_true_iff]
  exact ⟨hwin.1, fun h => hwin.2.1 (containsRequest_of_contains _ _ h), hwin.2.2⟩

theorem gameCore_eq_map_detailedGameCore (scheme : Scheme Generic.SecretKey)
    (adversary : Adversary) :
    gameCore scheme adversary = standardWon <$> detailedGameCore scheme adversary := by
  simp [gameCore, gameRest, detailedGameCore, detailedGameAfterKeygen, standardWon]

theorem forgeAdvantage_eq_detailedGameWithCache (scheme : Scheme Generic.SecretKey)
    (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome : GameOutcome × QueryCache HashSpec => standardWon outcome.1 = true |
        detailedGameWithCache scheme adversary] := by
  unfold forgeAdvantage detailedGameWithCache
  rw [gameCore_eq_map_detailedGameCore, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

theorem game_embed (adversary : AdversaryBridge.StatementAdversary) :
    gameCore Seeded.scheme (AdversaryBridge.embed adversary) = game Generic.xmss adversary := by
  unfold gameCore gameRest game
  rfl

theorem notion_advantage_eq (mode : Unforgeability.CountingMode) (adversary : AdversaryBridge.StatementAdversary) :
    (notion mode).advantage Generic.xmss adversary = forgeAdvantage Seeded.scheme (AdversaryBridge.embed adversary) := by
  rw [advantage_eq_game, ← game_embed]
  rfl

/-- info: 'Xmss.TargetSum.EUFCMA.notion_advantage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms notion_advantage_eq

end Xmss.TargetSum.EUFCMA

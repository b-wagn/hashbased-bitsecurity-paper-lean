import XmssSecurity.Proof.TargetSum.EUFCMA.Projection
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.Generic.DetailedExecution
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Standard freshness on the existing proof execution. The reference scheme's
cache and trace constructions can be reused without changing their executions. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

noncomputable def gameRest {Key : Type} (scheme : Generic.Scheme Key) (adversary : Generic.Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Generic.Forgery × QueryLog Generic.SigningSpec) ←
    (simulateQ (Generic.forwardOracles + Generic.signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SUFCMA.SigningTranscript.Valid log ∧
    ¬SigningTranscript.ContainsRequest log forgery) && verified

noncomputable def gameCore {Key : Type} (scheme : Generic.Scheme Key) (adversary : Generic.Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  gameRest scheme adversary pk sk

noncomputable def forgeAdvantage {Key : Type} (scheme : Generic.Scheme Key)
    (adversary : Generic.Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ Generic.romImpl (gameCore scheme adversary)).run' ∅]

def standardWon (outcome : Generic.GameOutcome) : Bool :=
  decide (SUFCMA.SigningTranscript.Valid outcome.signingLog ∧
    ¬SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery) && outcome.verified

theorem standardWon_eq_true_iff (outcome : Generic.GameOutcome) :
    standardWon outcome = true ↔ SUFCMA.SigningTranscript.Valid outcome.signingLog ∧
      ¬SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery ∧ outcome.verified = true := by
  simp [standardWon, and_assoc]

theorem strongWon_of_standardWon (outcome : Generic.GameOutcome) (hwin : standardWon outcome = true) :
    outcome.won = true := by
  rw [standardWon_eq_true_iff] at hwin
  rw [Generic.GameOutcome.won_eq_true_iff]
  exact ⟨hwin.1, fun h => hwin.2.1 (containsRequest_of_contains _ _ h), hwin.2.2⟩

theorem gameCore_eq_map_detailedGameCore (scheme : Generic.Scheme Generic.SecretKey)
    (adversary : Generic.Adversary) :
    gameCore scheme adversary = standardWon <$> Generic.detailedGameCore scheme adversary := by
  simp [gameCore, gameRest, Generic.detailedGameCore, Generic.detailedGameAfterKeygen, standardWon]

theorem forgeAdvantage_eq_detailedGameWithCache (scheme : Generic.Scheme Generic.SecretKey)
    (adversary : Generic.Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome : Generic.GameOutcome × QueryCache HashSpec => standardWon outcome.1 = true |
        Generic.detailedGameWithCache scheme adversary] := by
  unfold forgeAdvantage Generic.detailedGameWithCache
  rw [gameCore_eq_map_detailedGameCore, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

theorem game_embed (adversary : Generic.Security.StatementAdversary) :
    gameCore Generic.Seeded.scheme (Generic.Security.embed adversary) = game Generic.xmss adversary := by
  unfold gameCore gameRest game
  rfl

theorem notion_advantage_eq (mode : SUFCMA.CountingMode) (adversary : Generic.Security.StatementAdversary) :
    (notion mode).advantage Generic.xmss adversary = forgeAdvantage Generic.Seeded.scheme (Generic.Security.embed adversary) := by
  rw [advantage_eq_game, ← game_embed]
  rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.notion_advantage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms notion_advantage_eq

end XmssSecurity.TargetSum.EUFCMA

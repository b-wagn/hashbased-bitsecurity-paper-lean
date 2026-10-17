import XmssSecurity.Proof.TargetSum.EUFCMA.Projection
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.TargetSum.DetailedExecution

/-! Standard freshness on the existing proof execution. The reference scheme's
cache and trace constructions can be reused without changing their executions. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

noncomputable def gameRest {Key : Type} (scheme : Scheme Key) (adversary : XmssSecurity.TargetSum.Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SUFCMA.SigningTranscript.Valid log ∧
    ¬SigningTranscript.ContainsRequest log forgery) && verified

noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : XmssSecurity.TargetSum.Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  gameRest scheme adversary pk sk

noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key)
    (adversary : XmssSecurity.TargetSum.Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

def standardWon (outcome : GameOutcome) : Bool :=
  decide (SUFCMA.SigningTranscript.Valid outcome.signingLog ∧
    ¬SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery) && outcome.verified

theorem standardWon_eq_true_iff (outcome : GameOutcome) :
    standardWon outcome = true ↔ SUFCMA.SigningTranscript.Valid outcome.signingLog ∧
      ¬SigningTranscript.ContainsRequest outcome.signingLog outcome.forgery ∧ outcome.verified = true := by
  simp [standardWon, and_assoc]

theorem strongWon_of_standardWon (outcome : GameOutcome) (hwin : standardWon outcome = true) :
    outcome.won = true := by
  rw [standardWon_eq_true_iff] at hwin
  rw [GameOutcome.won_eq_true_iff]
  exact ⟨hwin.1, fun h => hwin.2.1 (containsRequest_of_contains _ _ h), hwin.2.2⟩

theorem gameCore_eq_map_detailedGameCore (scheme : Scheme SecretKey)
    (adversary : XmssSecurity.TargetSum.Adversary) :
    gameCore scheme adversary = standardWon <$> detailedGameCore scheme adversary := by
  simp [gameCore, gameRest, detailedGameCore, detailedGameAfterKeygen, standardWon]

theorem forgeAdvantage_eq_detailedGameWithCache (scheme : Scheme SecretKey)
    (adversary : XmssSecurity.TargetSum.Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun outcome : GameOutcome × QueryCache HashSpec => standardWon outcome.1 = true |
        detailedGameWithCache scheme adversary] := by
  unfold forgeAdvantage detailedGameWithCache
  rw [gameCore_eq_map_detailedGameCore, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

theorem game_embed (adversary : Security.StatementAdversary) :
    gameCore Seeded.scheme (Security.embed adversary) = game xmss adversary := by
  unfold gameCore gameRest game
  rfl

theorem notion_advantage_eq (mode : SUFCMA.CountingMode) (adversary : Security.StatementAdversary) :
    (notion mode).advantage xmss adversary = forgeAdvantage Seeded.scheme (Security.embed adversary) := by
  rw [advantage_eq_game, ← game_embed]
  rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.notion_advantage_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms notion_advantage_eq

end XmssSecurity.TargetSum.EUFCMA

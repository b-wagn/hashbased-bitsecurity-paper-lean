import XmssSecurity.Proof.Checksum.ConsistentQueryBound
import XmssSecurity.Proof.Checksum.Scheme.Xmss
import XmssSecurity.Proof.Common.Adversary.LegacyNotions
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# From the statement to the proof's game

The statement's SUF-CMA experiment for `xmss` (`SUFCMA.notionTotal xmss`) and the proof's internal
game for the seeded scheme (`gameCore Seeded.scheme`) are the same computation, so success
probabilities and hash-query counts transfer exactly.
-/

open OracleComp OracleSpec ENNReal
namespace XmssSecurity.Checksum.Security

set_option backward.isDefEq.respectTransparency false

/-- The statement's adversary type and the proof's are the same. -/
abbrev StatementAdversary := SUFCMA.Adversary OracleWorld PublicKey Message Signature lifetime

def embed (adversary : StatementAdversary) : XmssSecurity.Checksum.Adversary :=
  ⟨adversary.main⟩

theorem game_embed (adversary : StatementAdversary) :
    XmssSecurity.Checksum.gameCore Seeded.scheme (embed adversary) = SUFCMA.game xmss adversary := by
  unfold XmssSecurity.Checksum.gameCore Seeded.gameRest SUFCMA.game
  rfl

/-- The proof's counted random oracle is the statement's. -/
theorem countedRomImpl_eq :
    countedRomImpl = RandomOracleModel.countedImpl HashInput HashOutput := by
  funext input
  cases input <;> rfl

theorem experiment_embed (adversary : StatementAdversary) :
    (simulateQ countedRomImpl (XmssSecurity.Checksum.gameCore Seeded.scheme (embed adversary))).run.run' ∅ =
      SUFCMA.notionTotal.experiment xmss adversary := by
  rw [game_embed, countedRomImpl_eq]
  rfl

theorem advantage_embed (adversary : StatementAdversary) :
    XmssSecurity.Checksum.forgeAdvantage Seeded.scheme (embed adversary) =
      SUFCMA.notionTotal.advantage xmss adversary := by
  unfold SecurityNotion.advantage XmssSecurity.Checksum.forgeAdvantage
  rw [← experiment_embed, ← simulateQ_countHashQueries]
  have h := congrArg (fun computation : OracleComp OracleWorld Bool =>
    (simulateQ romImpl computation).run' ∅)
    (countHashQueries_forget (XmssSecurity.Checksum.gameCore Seeded.scheme (embed adversary)))
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h]
  simpa only [probEvent_eq_eq_probOutput, Function.comp_def] using probEvent_map (mx := (simulateQ romImpl
    (countHashQueries (XmssSecurity.Checksum.gameCore Seeded.scheme (embed adversary)))).run' ∅)
    (f := Prod.fst) (q := fun result => result = true)

end XmssSecurity.Checksum.Security

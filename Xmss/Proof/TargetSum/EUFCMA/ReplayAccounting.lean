import Xmss.Proof.TargetSum.EUFCMA.ReplaySeeded
import Xmss.Proof.TargetSum.EUFCMA.DirectBridge
import Xmss.Proof.Generic.Scheme.Xmss
import Xmss.Statement.UnforgeabilityGame
import Xmss.Proof.Common.Legacy.PerModeNotionsEUFCMA
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The replay/fallback adversary has semantic direct budget one and refutes
127-bit standard unforgeability of the original seeded scheme in that mode. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

attribute [local irreducible] Generic.sampleMasterSeed

theorem replay_gameCounted_direct :
    SUFCMA.gameCountedDirect (RandomOracleModel.hashCost HashInput Digest) Generic.xmss replayStatementAdversary =
      (fun result => (result, 1)) <$> SUFCMA.game Generic.xmss replayStatementAdversary := by
  unfold SUFCMA.gameCountedDirect SUFCMA.game
  simp only [map_bind, map_pure]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [AdversaryBridge.run_withAddCost_eq_counted _ _ (fun input => by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash <;> rfl
    · rfl)]
  change (do
    let result ← (simulateQ (AdversaryBridge.adversaryImpl secretKey)
      (QueryCounting.counted Direct.IsDirectHashQuery (replayMain publicKey))).run
    let verified ← Generic.xmss.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature
    return (decide (Unforgeability.SigningTranscript.Valid result.2 ∧
      ¬Unforgeability.SigningTranscript.Contains result.2 result.1.1) && verified, result.1.2)) = _
  rw [replayMain_counted]
  simp only [simulateQ_map, WriterT.run_map', bind_map_left]
  rfl

theorem replay_statement_direct_queryBound :
    (notion Unforgeability.CountingMode.direct).HasQueryBound Generic.xmss replayStatementAdversary 1 := by
  rw [direct_queryBound_iff_strong_legacy]
  intro result hresult
  change result ∈ support (RandomOracleModel.run
    (SUFCMA.gameCountedDirect (RandomOracleModel.hashCost HashInput Digest) Generic.xmss replayStatementAdversary)) at hresult
  rw [replay_gameCounted_direct] at hresult
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_map', support_map, Set.mem_image] at hresult
  obtain ⟨won, _, rfl⟩ := hresult
  exact le_rfl

theorem replay_direct_attack_126 : ¬(EUFCMA.notion Unforgeability.CountingMode.direct).HasClassicalSecurityBits Generic.xmss (126 + 1) := by
  intro hsecure
  have hbound := hsecure 1 le_rfl replayStatementAdversary replay_statement_direct_queryBound
  rw [notion_advantage_eq, Nat.cast_one, one_div] at hbound
  exact (not_lt_of_ge hbound) replay_seeded_advantage_exceeds_127

/-- info: 'Xmss.TargetSum.EUFCMA.replay_direct_attack_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_direct_attack_126

end Xmss.TargetSum.EUFCMA

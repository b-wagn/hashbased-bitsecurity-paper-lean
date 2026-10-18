import XmssSecurity.Proof.TargetSum.EUFCMA.ReplaySeeded
import XmssSecurity.Proof.TargetSum.EUFCMA.DirectBridge
import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-! The replay/fallback adversary has semantic direct budget one and refutes
127-bit standard unforgeability of the original seeded scheme in that mode. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

attribute [local irreducible] sampleMasterSeed

theorem replay_gameCounted_direct :
    SUFCMA.gameCountedDirect (RandomOracleModel.hashCost HashInput HashOutput) xmss replayStatementAdversary =
      (fun result => (result, 1)) <$> SUFCMA.game xmss replayStatementAdversary := by
  unfold SUFCMA.gameCountedDirect SUFCMA.game
  simp only [map_bind, map_pure]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [Security.run_withAddCost_eq_counted _ _ (fun input => by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash <;> rfl
    · rfl)]
  change (do
    let result ← (simulateQ (Security.adversaryImpl secretKey)
      (QueryCounting.counted Direct.IsDirectHashQuery (replayMain publicKey))).run
    let verified ← xmss.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature
    return (decide (SUFCMA.SigningTranscript.Valid result.2 ∧
      ¬SUFCMA.SigningTranscript.Contains result.2 result.1.1) && verified, result.1.2)) = _
  rw [replayMain_counted]
  simp only [simulateQ_map, WriterT.run_map', bind_map_left]
  rfl

theorem replay_statement_direct_queryBound :
    (notion SUFCMA.CountingMode.direct).HasQueryBound xmss replayStatementAdversary 1 := by
  rw [direct_queryBound_iff_strong_legacy]
  intro result hresult
  change result ∈ support (RandomOracleModel.run
    (SUFCMA.gameCountedDirect (RandomOracleModel.hashCost HashInput HashOutput) xmss replayStatementAdversary)) at hresult
  rw [replay_gameCounted_direct] at hresult
  simp only [RandomOracleModel.run, simulateQ_map, StateT.run'_map', support_map, Set.mem_image] at hresult
  obtain ⟨won, _, rfl⟩ := hresult
  exact le_rfl

theorem replay_direct_attack_126 : ¬(EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss (126 + 1) := by
  intro hsecure
  have hbound := hsecure 1 le_rfl replayStatementAdversary replay_statement_direct_queryBound
  rw [notion_advantage_eq, Nat.cast_one, one_div] at hbound
  exact (not_lt_of_ge hbound) replay_seeded_advantage_exceeds_127

/-- info: 'XmssSecurity.TargetSum.EUFCMA.replay_direct_attack_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms replay_direct_attack_126

end XmssSecurity.TargetSum.EUFCMA

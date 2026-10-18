import XmssSecurity.Proof.Common.EUFCMA.Modes
import XmssSecurity.Proof.Common.Modes.Direct
import XmssSecurity.Proof.Generic.Direct.Bridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Forgetting charges recovers the uncounted standard-forgery game. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open SUFCMA hiding experiment game gameCounted notion securityGame

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

theorem map_fst_gameCounted_direct [DecidableEq Msg] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) :
    Prod.fst <$> gameCounted CountingMode.direct cost scheme adversary = game scheme adversary := by
  unfold gameCounted game
  simp only [CountingMode.direct, costIf, Bool.false_eq_true, if_false, Modes.charge_zero,
    Modes.impl_direct_eq, bind_map_left, map_bind, map_pure, zero_add, add_zero]
  apply bind_congr
  rintro ⟨pk, sk⟩
  exact Security.bind_map_fst_eq _ _ _ (fun result => do
    let verified ← scheme.verify pk result.1.epoch result.1.message result.1.signature
    pure (decide (SUFCMA.SigningTranscript.Valid result.2 ∧
      ¬SigningTranscript.ContainsRequest result.2 result.1) && verified))

theorem map_fst_gameCounted [DecidableEq Msg] (mode : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) :
    Prod.fst <$> gameCounted mode cost scheme adversary = game scheme adversary := by
  have h : ∀ m : CountingMode, Prod.fst <$> gameCounted m cost scheme adversary =
      Prod.fst <$> gameDetailed cost scheme adversary := fun m => by
    rw [gameCounted_eq_map_gameDetailed, Functor.map_map]
  rw [h mode, ← h CountingMode.direct, map_fst_gameCounted_direct]

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output] [DecidableEq Msg]

theorem advantage_eq_game (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion mode).advantage scheme adversary =
      Pr[= true | RandomOracleModel.run (game scheme adversary)] := by
  rw [← map_fst_gameCounted mode (RandomOracleModel.hashCost Input Output)]
  simp only [SecurityNotion.advantage, notion, RandomOracleModel.run, simulateQ_map,
    StateT.run'_map', ← probEvent_eq_eq_probOutput, probEvent_map]
  rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.advantage_eq_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms advantage_eq_game

end XmssSecurity.TargetSum.EUFCMA

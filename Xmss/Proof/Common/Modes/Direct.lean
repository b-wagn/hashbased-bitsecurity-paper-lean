import Xmss.Proof.Common.Adversary.LegacyNotions

/-!
# The direct counting mode is the legacy direct notion

`SUFCMA.notion CountingMode.direct` charges only the adversary's own hash calls; this file shows
that it is the legacy `SUFCMA.notionDirect`.
-/

open OracleComp OracleSpec ENNReal

namespace Xmss.Modes

open Unforgeability SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- Charging nothing only pairs the result with `0`. -/
theorem charge_zero {α : Type} (computation : OracleComp spec α) :
    charge (fun _ => 0) computation = (fun a => (a, 0)) <$> computation := by
  simp [charge, addCostOracle, QueryImpl.withAddCost, ofAdd_zero,
    QueryImpl.run_simulateQ_withCost_const_one, Functor.map_map]

/-- Charging zero units is a no-op. -/
theorem addTell_zero {M : Type → Type} [Monad M] :
    AddWriterT.addTell (M := M) (0 : ℕ) = pure ⟨⟩ := by
  simp only [AddWriterT.addTell, ofAdd_zero]
  rfl

/-- Lifting through the charged run records the unit charge. -/
theorem run_liftM_chargedRun {α : Type} (computation : OracleComp spec α) :
    (liftM computation : ChargedRun spec Msg Sig L α).run =
      (fun a => (a, 1)) <$>
        (liftM computation : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) α) :=
  rfl

/-- Lifting a logged computation into the charged run records the unit charge. -/
theorem run_liftM_chargedRun' {α : Type}
    (computation : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) α) :
    (liftM computation : ChargedRun spec Msg Sig L α).run = (fun a => (a, 1)) <$> computation :=
  rfl

/-- Lifting into the logged run records the empty log. -/
theorem run_liftM_logged {α : Type} (computation : OracleComp spec α) :
    (liftM computation : WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec) α).run =
      (fun a => (a, ∅)) <$> computation :=
  rfl

/-- The signing oracle charging nothing is the logged signing oracle lifted to the charged run. -/
theorem signingOracleCounted_zero (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK)
    (request : SignRequest Msg L) :
    signingOracleCounted (fun _ => 0) 0 scheme sk request =
      (liftM (signingOracle scheme sk request) : ChargedRun spec Msg Sig L (Option Sig)) := by
  refine WriterT.ext _ _ ?_
  simp only [signingOracleCounted, charge_zero, signingOracle, QueryImpl.withLogging_apply]
  refine WriterT.ext _ _ ?_
  simp only [WriterT.run_bind, run_liftM_chargedRun, run_liftM_chargedRun', run_liftM_logged,
    WriterT.run_tell, WriterT.run_pure, add_zero, addTell_zero, map_bind, bind_map_left,
    Functor.map_map, pure_bind, map_pure, one_mul, mul_one, LawfulAppend.empty_append,
    LawfulAppend.append_empty]

/-- The combined implementation of the direct mode is the one of the legacy direct game. -/
theorem impl_direct_eq (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L) (sk : SK) :
    (QueryImpl.ofLift spec
        (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
      signingOracleCounted (fun _ => 0) 0 scheme sk =
    (QueryImpl.ofLift spec (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec)) +
        signingOracle scheme sk).withAddCost (fun | .inl input => cost input | .inr _ => 0) := by
  funext t
  rcases t with t | request
  · simp only [QueryImpl.add_apply_inl, QueryImpl.withAddCost_apply]
    rfl
  · simp only [QueryImpl.add_apply_inr, QueryImpl.withAddCost_apply, signingOracleCounted_zero,
      addTell_zero, pure_bind]
    rfl

/-- The counted game of the direct mode is the legacy direct game. -/
theorem gameCounted_direct_eq [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) :
    gameCounted CountingMode.direct cost scheme adversary =
      gameCountedDirect cost scheme adversary := by
  unfold gameCounted gameCountedDirect
  simp only [CountingMode.direct, costIf, Bool.false_eq_true, if_false, charge_zero,
    impl_direct_eq, bind_map_left]
  congr 1
  funext keys
  rcases keys with ⟨pk, sk⟩
  dsimp only
  congr 1
  funext result
  rcases result with ⟨⟨forgery, charged⟩, log⟩
  dsimp only
  simp only [zero_add, add_zero]

section RandomOracleModel

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]
  [DecidableEq Msg] [DecidableEq Sig]
  (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
  (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L)

/-- The experiment of the direct mode is the experiment of the legacy direct notion. -/
theorem notion_direct_experiment_eq :
    (notion CountingMode.direct).experiment scheme adversary =
      notionDirect.experiment scheme adversary := by
  simp only [notion, notionDirect]
  rw [gameCounted_direct_eq]
  refine congrArg (fun c => RandomOracleModel.run (gameCountedDirect c scheme adversary)) ?_
  funext t
  rcases t with t | t <;> rfl

/-- The advantage in the direct mode is the advantage in the legacy direct notion. -/
theorem notion_direct_advantage_eq :
    (notion CountingMode.direct).advantage scheme adversary =
      notionDirect.advantage scheme adversary := by
  unfold SecurityNotion.advantage
  rw [notion_direct_experiment_eq]

/-- Query bounds agree between the direct mode and the legacy direct notion. -/
theorem notion_direct_hasQueryBound_iff (q : ℕ) :
    (notion CountingMode.direct).HasQueryBound scheme adversary q ↔
      notionDirect.HasQueryBound scheme adversary q := by
  unfold SecurityNotion.HasQueryBound
  rw [notion_direct_experiment_eq]

/-- Classical security bits agree between the direct mode and the legacy direct notion. -/
theorem notion_direct_hasClassicalSecurityBits_iff (bits : ℕ) :
    (notion CountingMode.direct).HasClassicalSecurityBits scheme bits ↔
      notionDirect.HasClassicalSecurityBits scheme bits := by
  unfold SecurityNotion.HasClassicalSecurityBits
  constructor
  · intro h q hq adversary hbound
    exact (notion_direct_advantage_eq scheme adversary).symm.trans_le
      (h q hq adversary ((notion_direct_hasQueryBound_iff scheme adversary q).2 hbound))
  · intro h q hq adversary hbound
    exact (notion_direct_advantage_eq scheme adversary).trans_le
      (h q hq adversary ((notion_direct_hasQueryBound_iff scheme adversary q).1 hbound))

end RandomOracleModel

end Xmss.Modes

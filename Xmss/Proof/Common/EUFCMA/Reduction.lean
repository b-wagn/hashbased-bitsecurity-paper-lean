import Xmss.Statement.UnforgeabilityGame
import Xmss.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-! Standard and strong unforgeability use identical executions and query charges.
Only the final freshness predicate differs. This transfers every strong-security
lower bound without changing the adversary or its semantic query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Xmss.EUFCMA

open Unforgeability SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

theorem containsRequest_of_contains [DecidableEq Msg] [DecidableEq Sig]
    (log : QueryLog (SigningSpec Msg Sig L)) (forgery : Forgery Msg Sig L)
    (h : Unforgeability.SigningTranscript.Contains log forgery) :
    Unforgeability.SigningTranscript.ContainsRequest log forgery := by
  obtain ⟨entry, hentry, hrequest, _⟩ := h
  exact ⟨entry, hentry, hrequest⟩

/-- The common execution, retaining the data needed by both winning predicates. -/
structure CountedOutcome (Msg Sig : Type) (L : ℕ) where
  forgery : Forgery Msg Sig L
  log : QueryLog (SigningSpec Msg Sig L)
  verified : Bool
  charged : ℕ

def CountedOutcome.standardResult [DecidableEq Msg] (outcome : CountedOutcome Msg Sig L) : Bool × ℕ :=
  (decide (Unforgeability.SigningTranscript.Valid outcome.log ∧
    ¬Unforgeability.SigningTranscript.ContainsRequest outcome.log outcome.forgery) && outcome.verified, outcome.charged)

def CountedOutcome.strongResult [DecidableEq Msg] [DecidableEq Sig]
    (outcome : CountedOutcome Msg Sig L) : Bool × ℕ :=
  (decide (Unforgeability.SigningTranscript.Valid outcome.log ∧
    ¬Unforgeability.SigningTranscript.Contains outcome.log outcome.forgery) && outcome.verified, outcome.charged)

theorem CountedOutcome.strongWin_of_standardWin [DecidableEq Msg] [DecidableEq Sig]
    (outcome : CountedOutcome Msg Sig L) (hwin : outcome.standardResult.1 = true) :
    outcome.strongResult.1 = true := by
  simp only [standardResult, Bool.and_eq_true, decide_eq_true_eq] at hwin
  simp only [strongResult, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hwin.1.1, fun h => hwin.1.2 (containsRequest_of_contains _ _ h)⟩, hwin.2⟩

def recordedGame (mode : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary spec PK Msg Sig L) : OracleComp spec (CountedOutcome Msg Sig L) := do
  let ((pk, sk), keygenCharged) ← charge (costIf mode.keygen cost) scheme.keygen
  let (((forgery, adversaryCharged), log) :
      (Forgery Msg Sig L × Multiplicative ℕ) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
        signingOracleCounted (costIf mode.signer cost) (if mode.requests then 1 else 0) scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCharged) ← charge (costIf mode.verifier cost)
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return ⟨forgery, log, verified, keygenCharged + Multiplicative.toAdd adversaryCharged + verifierCharged⟩

theorem gameCounted_eq_map_recordedGame [DecidableEq Msg]
    (mode : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary spec PK Msg Sig L) :
    gameCounted mode cost scheme adversary = CountedOutcome.standardResult <$> recordedGame mode cost scheme adversary := by
  unfold gameCounted recordedGame
  simp only [map_bind]
  apply bind_congr
  rintro ⟨⟨pk, sk⟩, keygenCharged⟩
  apply bind_congr
  rintro ⟨⟨forgery, adversaryCharged⟩, log⟩
  simp only [map_pure]
  rfl

theorem strong_gameCounted_eq_map_recordedGame [DecidableEq Msg] [DecidableEq Sig]
    (mode : CountingMode) (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary spec PK Msg Sig L) :
    SUFCMA.gameCounted mode cost scheme adversary =
      CountedOutcome.strongResult <$> recordedGame mode cost scheme adversary := by
  unfold SUFCMA.gameCounted recordedGame
  simp only [map_bind]
  apply bind_congr
  rintro ⟨⟨pk, sk⟩, keygenCharged⟩
  apply bind_congr
  rintro ⟨⟨forgery, adversaryCharged⟩, log⟩
  simp only [map_pure]
  rfl

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]
variable [DecidableEq Msg] [DecidableEq Sig]

noncomputable def recordedExperiment (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    ProbComp (CountedOutcome Msg Sig L) :=
  RandomOracleModel.run (recordedGame mode (RandomOracleModel.hashCost Input Output) scheme adversary)

omit [DecidableEq Sig] in
theorem experiment_eq_map_recordedExperiment (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion mode).experiment scheme adversary =
      CountedOutcome.standardResult <$> recordedExperiment mode scheme adversary := by
  simp only [notion, recordedExperiment, RandomOracleModel.run,
    gameCounted_eq_map_recordedGame, simulateQ_map, StateT.run'_map']

theorem strong_experiment_eq_map_recordedExperiment (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (SUFCMA.notion mode).experiment scheme adversary =
      CountedOutcome.strongResult <$> recordedExperiment mode scheme adversary := by
  simp only [SUFCMA.notion, recordedExperiment, RandomOracleModel.run,
    strong_gameCounted_eq_map_recordedGame, simulateQ_map, StateT.run'_map']

theorem hasQueryBound_iff_strong (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) (q : ℕ) :
    (notion mode).HasQueryBound scheme adversary q ↔
      (SUFCMA.notion mode).HasQueryBound scheme adversary q := by
  unfold SecurityNotion.HasQueryBound
  rw [experiment_eq_map_recordedExperiment, strong_experiment_eq_map_recordedExperiment]
  constructor
  · intro h result hresult
    rw [support_map] at hresult
    obtain ⟨outcome, houtcome, rfl⟩ := hresult
    exact h outcome.standardResult (by rw [support_map]; exact ⟨outcome, houtcome, rfl⟩)
  · intro h result hresult
    rw [support_map] at hresult
    obtain ⟨outcome, houtcome, rfl⟩ := hresult
    exact h outcome.strongResult (by rw [support_map]; exact ⟨outcome, houtcome, rfl⟩)

theorem advantage_le_strong (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Unforgeability.Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion mode).advantage scheme adversary ≤ (SUFCMA.notion mode).advantage scheme adversary := by
  unfold SecurityNotion.advantage
  rw [experiment_eq_map_recordedExperiment, strong_experiment_eq_map_recordedExperiment, probEvent_map, probEvent_map]
  apply probEvent_mono''
  intro outcome hwin
  exact outcome.strongWin_of_standardWin hwin

theorem security_of_strong (mode : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L) (bits : ℕ)
    (hstrong : (SUFCMA.notion mode).HasClassicalSecurityBits scheme bits) :
    (notion mode).HasClassicalSecurityBits scheme bits := by
  intro q hq adversary hbudget
  exact (advantage_le_strong mode scheme adversary).trans
    (hstrong q hq adversary ((hasQueryBound_iff_strong mode scheme adversary q).1 hbudget))

/-- info: 'Xmss.EUFCMA.security_of_strong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms security_of_strong

end Xmss.EUFCMA

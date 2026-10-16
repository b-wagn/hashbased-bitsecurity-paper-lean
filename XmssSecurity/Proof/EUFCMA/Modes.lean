import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Modes.Lattice
import XmssSecurity.Proof.Legacy.PerModeNotionsEUFCMA

/-! Counting-mode monotonicity for standard unforgeability. The shared accounting
lemmas retain the standard freshness predicate throughout the experiment. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA

open SUFCMA XmssSecurity.Modes

section game

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

/-- The experiment as `gameCounted`, returning the charge per kind instead of its weighted sum. -/
def gameDetailed [DecidableEq Msg] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) : OracleComp spec (Bool × Charges) := do
  let ((pk, sk), keygenCharged) ← chargeWith (fun t => Kind.single .keygen (cost t)) scheme.keygen
  let (((forgery, adversaryCharged), log) :
      (Forgery Msg Sig L × Multiplicative Charges) × QueryLog (SigningSpec Msg Sig L)) ←
    (simulateQ
      ((QueryImpl.ofLift spec
          (WriterT (QueryLog (SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost
            (fun t => Kind.single .hash (cost t)) +
        signingOracleDetailed cost scheme sk)
      (adversary.main pk)).run.run
  let (verified, verifierCharged) ← chargeWith (fun t => Kind.single .verifier (cost t))
    (scheme.verify pk forgery.epoch forgery.message forgery.signature)
  return (decide (SUFCMA.SigningTranscript.Valid log ∧ ¬SigningTranscript.ContainsRequest log forgery) && verified,
    keygenCharged + Multiplicative.toAdd adversaryCharged + verifierCharged)

/-- The counted experiment of a mode is the detailed one with its charge weighted. -/
theorem gameCounted_eq_map_gameDetailed [DecidableEq Msg] (m : CountingMode)
    (cost : spec.Domain → ℕ) (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : Adversary spec PK Msg Sig L) :
    gameCounted m cost scheme adversary =
      (fun r => (r.1, m.weight r.2)) <$> gameDetailed cost scheme adversary := by
  unfold gameCounted gameDetailed
  rw [charge_eq_chargeWith, chargeWith_eq_map m.weight (m.weight_single_keygen cost)]
  simp only [map_bind, bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨pk, sk⟩, keygenCharged⟩
  dsimp only
  rw [simulateQ_counted_eq_relabelT m, run_relabelT, WriterT.run_map']
  simp only [bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨forgery, adversaryCharged⟩, log⟩
  dsimp only [Prod.map, relabel, id]
  rw [charge_eq_chargeWith, chargeWith_eq_map m.weight (m.weight_single_verifier cost)]
  simp only [bind_map_left]
  refine bind_congr fun r => ?_
  rcases r with ⟨verified, verifierCharged⟩
  simp only [map_pure, map_add, toAdd_ofAdd]
  rfl

end game

section monotone

variable {PK SK Msg Sig : Type} {L : ℕ} {Input Output : Type} [DecidableEq Input]
  [SampleableType Output] [DecidableEq Msg]

/-- The experiment of `notion m` is the detailed experiment with its charge weighted by `m`. -/
lemma experiment_notion_eq (m : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion m).experiment scheme adversary =
      (fun r => (r.1, m.weight r.2)) <$>
        RandomOracleModel.run (gameDetailed (RandomOracleModel.hashCost Input Output) scheme
          adversary) := by
  simp only [notion, RandomOracleModel.run, gameCounted_eq_map_gameDetailed, simulateQ_map,
    StateT.run'_map']

/-- The winning probability does not depend on the counting mode. -/
theorem advantage_eq_of_mode (m m' : CountingMode)
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) :
    (notion m).advantage scheme adversary = (notion m').advantage scheme adversary := by
  simp only [SecurityNotion.advantage, experiment_notion_eq, probEvent_map]
  rfl

/-- A query bound for a mode is a query bound for every mode charging less. -/
theorem hasQueryBound_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (adversary : Adversary (RandomOracleModel.World Input Output) PK Msg Sig L) (q : ℕ)
    (hq : (notion m').HasQueryBound scheme adversary q) :
    (notion m).HasQueryBound scheme adversary q := by
  intro r hr
  rw [experiment_notion_eq, support_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  refine le_trans (CountingMode.weight_le_weight h s.2) ?_
  exact hq _ (by rw [experiment_notion_eq, support_map]; exact ⟨s, hs, rfl⟩)

/-- Security for a mode is security for every mode charging more. -/
theorem hasClassicalSecurityBits_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) (hs : (notion m).HasClassicalSecurityBits scheme bits) :
    (notion m').HasClassicalSecurityBits scheme bits := by
  intro q hq adversary hb
  rw [advantage_eq_of_mode m' m]
  exact hs q hq adversary (hasQueryBound_of_le h scheme adversary q hb)

/-- An attack on a mode is an attack on every mode charging less. -/
theorem not_hasClassicalSecurityBits_of_le {m m' : CountingMode} (h : m.Le m')
    (scheme : EpochBasedSignature (RandomOracleModel.World Input Output) PK SK Msg Sig L)
    (bits : ℕ) (hs : ¬ (notion m').HasClassicalSecurityBits scheme bits) :
    ¬ (notion m).HasClassicalSecurityBits scheme bits :=
  fun hm => hs (hasClassicalSecurityBits_of_le h scheme bits hm)

end monotone

/-- info: 'XmssSecurity.EUFCMA.hasClassicalSecurityBits_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasClassicalSecurityBits_of_le

end XmssSecurity.EUFCMA

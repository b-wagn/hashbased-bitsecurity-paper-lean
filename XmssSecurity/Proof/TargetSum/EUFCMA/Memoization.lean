import XmssSecurity.Proof.TargetSum.EUFCMA.SeededTable
import XmssSecurity.Proof.Generic.Deterministic.MemoTable
import XmssSecurity.Proof.Generic.Deterministic.RequestSampling
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Memoizing repeated signing inputs preserves standard winning executions.
The standard freshness predicate is monotone when the forwarded log is shortened. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

def transcriptWin (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool) : Bool :=
  decide (SUFCMA.SigningTranscript.Valid log ∧ ¬EUFCMA.SigningTranscript.ContainsRequest log forgery) && verified

theorem transcriptWin_mono (forgery : Forgery) (original forwarded : QueryLog SigningSpec)
    (h : forwarded.Sublist original) (verified : Bool) (hwin : transcriptWin forgery original verified = true) :
    transcriptWin forgery forwarded verified = true := by
  simp only [transcriptWin, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  refine ⟨⟨List.Nodup.sublist (h.map _) hwin.1.1, ?_⟩, hwin.2⟩
  rintro ⟨entry, hentry, heq⟩
  exact hwin.1.2 ⟨entry, h.subset hentry, heq⟩

noncomputable def finishGame (publicKey : PublicKey) (result : Forgery × QueryLog SigningSpec) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (Generic.Concrete.verify publicKey result.1.epoch result.1.message result.1.signature : OracleComp HashSpec Bool)
  return transcriptWin result.1 result.2 verified

noncomputable def sourceGame (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) Bool :=
  DeterministicSigning.withRequestLog (adversary.main publicKey) >>= fun result => DeterministicSigning.baseLift (finishGame publicKey result)

noncomputable def transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) (Bool × Bool) := do
  let result ← DeterministicSigning.withRequestLog (DeterministicSigning.memoize (DeterministicSigning.withRequestLog (adversary.main publicKey)) ∅)
  let verified ← DeterministicSigning.baseLift (liftM
    (Generic.Concrete.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return (transcriptWin result.1.1 result.1.2 verified, transcriptWin result.1.1 result.2 verified)

theorem runSigning_sourceGame (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    Seeded.runSigning (fun (request : SignRequest) => Seeded.tableSign randomizers secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest (Seeded.tableScheme randomizers) adversary publicKey secretKey := by
  simp only [sourceGame, Seeded.runSigning, simulateQ_bind, DeterministicSigning.simulateQ_baseLift, simulateQ_ofLift_eq_self]
  rw [show simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
      fun (request : SignRequest) => liftM (Seeded.tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Generic.Signature)))
      (DeterministicSigning.withRequestLog (adversary.main publicKey)) =
        Seeded.loggedRun (fun (request : SignRequest) => liftM (Seeded.tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Generic.Signature)))
          (adversary.main publicKey) from Seeded.runSigning_withRequestLog _ _]
  unfold Seeded.loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem fst_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.fst <$> transcriptReduction publicKey adversary = DeterministicSigning.memoize (sourceGame publicKey adversary) ∅ := by
  unfold transcriptReduction sourceGame
  rw [DeterministicSigning.memoize_baseLift_bind]
  conv_rhs => rw [← DeterministicSigning.fst_withRequestLog (DeterministicSigning.memoize (DeterministicSigning.withRequestLog (adversary.main publicKey)) ∅)]
  simp only [map_bind, bind_map_left, map_pure, finishGame, DeterministicSigning.baseLift, simulateQ_bind, simulateQ_pure]

theorem snd_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.snd <$> transcriptReduction publicKey adversary = sourceGame publicKey (Seeded.memoAdversary adversary) := by
  unfold transcriptReduction sourceGame Seeded.memoAdversary
  rw [← DeterministicSigning.withRequestLog_memoize_forget (adversary.main publicKey) ∅]
  simp only [map_bind, bind_map_left, map_pure, finishGame, DeterministicSigning.baseLift, simulateQ_bind, simulateQ_pure]

theorem transcriptReduction_win (publicKey : PublicKey) (adversary : Adversary)
    (result : Bool × Bool) (hresult : result ∈ support (transcriptReduction publicKey adversary)) :
    result.1 = true → result.2 = true := by
  simp only [transcriptReduction, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨logs, hlogs, verified, _, rfl⟩ := hresult
  exact transcriptWin_mono _ _ _ (DeterministicSigning.memoize_log_sublist _ ∅ logs hlogs) verified

theorem prob_sourceGame_le_memo (sign : SignRequest → OracleComp HashSpec (Option Generic.Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) :
    Pr[= true | Seeded.evaluateSource sign (sourceGame publicKey adversary) cache] ≤
      Pr[= true | Seeded.evaluateSource sign (sourceGame publicKey (Seeded.memoAdversary adversary)) cache] := by
  unfold Seeded.evaluateSource
  rw [probOutput_congr rfl (Seeded.evalDist_runSigning_memoize sign (sourceGame publicKey adversary) cache)]
  change Pr[= true | Seeded.evaluateSource sign (DeterministicSigning.memoize (sourceGame publicKey adversary) ∅) cache] ≤
    Pr[= true | Seeded.evaluateSource sign (sourceGame publicKey (Seeded.memoAdversary adversary)) cache]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, Seeded.evaluateSource_map, Seeded.evaluateSource_map]
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  exact transcriptReduction_win publicKey adversary result (Seeded.evaluateSource_support sign _ cache hresult) hwin

theorem prob_tableGameAfterSecrets_le_memo (adversary : Adversary) (parameter : PublicParameter)
    (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ romImpl (tableGameAfterSecrets adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ romImpl (tableGameAfterSecrets (Seeded.memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterSecrets
  rw [Seeded.run'_lift_hash_bind, Seeded.run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem prob_independentTableGame_le_memo (adversary : Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (Seeded.memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterSecrets_le_memo _ _ _ _ ∅

theorem freshRequests_sourceGame_memo (publicKey : PublicKey) (adversary : Adversary) :
    DeterministicSigning.FreshRequests ∅ (sourceGame publicKey (Seeded.memoAdversary adversary)) := by
  have h : DeterministicSigning.FreshRequests ∅ (DeterministicSigning.memoize (adversary.main publicKey) ∅) := by
    simpa only [QueryCache.empty_apply, ne_eq, not_true_eq_false, Set.setOf_false] using
      DeterministicSigning.freshRequests_memoize (adversary.main publicKey) ∅
  unfold sourceGame Seeded.memoAdversary
  apply h.withRequestLog.bind
  intro result used
  rw [← bind_pure (DeterministicSigning.baseLift (finishGame publicKey result))]
  exact DeterministicSigning.freshRequests_base_bind used (finishGame publicKey result) _ (fun value => .pure value)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.prob_independentTableGame_le_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prob_independentTableGame_le_memo

end XmssSecurity.TargetSum.EUFCMA.Seeded

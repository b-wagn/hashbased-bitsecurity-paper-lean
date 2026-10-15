import XmssSecurity.Proof.EUFCMA.SeededTable
import XmssSecurity.Proof.Deterministic.MemoTable
import XmssSecurity.Proof.Deterministic.RequestSampling

/-! Memoizing repeated signing inputs preserves standard winning executions.
The standard freshness predicate is monotone when the forwarded log is shortened. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA.Seeded

open XmssSecurity.Seeded DeterministicSigning

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
  let verified ← liftM (Concrete.verify publicKey result.1.epoch result.1.message result.1.signature : OracleComp HashSpec Bool)
  return transcriptWin result.1 result.2 verified

noncomputable def sourceGame (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) Bool :=
  withRequestLog (adversary.main publicKey) >>= fun result => baseLift (finishGame publicKey result)

noncomputable def transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) (Bool × Bool) := do
  let result ← withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)
  let verified ← baseLift (liftM
    (Concrete.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return (transcriptWin result.1.1 result.1.2 verified, transcriptWin result.1.1 result.2 verified)

theorem runSigning_sourceGame (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    runSigning (fun (request : SignRequest) => tableSign randomizers secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest (tableScheme randomizers) adversary publicKey secretKey := by
  simp only [sourceGame, runSigning, simulateQ_bind, simulateQ_baseLift, simulateQ_ofLift_eq_self]
  rw [show simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
      fun (request : SignRequest) => liftM (tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Signature)))
      (withRequestLog (adversary.main publicKey)) =
        loggedRun (fun (request : SignRequest) => liftM (tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Signature)))
          (adversary.main publicKey) from runSigning_withRequestLog _ _]
  unfold loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem fst_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.fst <$> transcriptReduction publicKey adversary = memoize (sourceGame publicKey adversary) ∅ := by
  unfold transcriptReduction sourceGame
  rw [memoize_baseLift_bind]
  conv_rhs => rw [← fst_withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem snd_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.snd <$> transcriptReduction publicKey adversary = sourceGame publicKey (memoAdversary adversary) := by
  unfold transcriptReduction sourceGame memoAdversary
  rw [← withRequestLog_memoize_forget (adversary.main publicKey) ∅]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem transcriptReduction_win (publicKey : PublicKey) (adversary : Adversary)
    (result : Bool × Bool) (hresult : result ∈ support (transcriptReduction publicKey adversary)) :
    result.1 = true → result.2 = true := by
  simp only [transcriptReduction, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨logs, hlogs, verified, _, rfl⟩ := hresult
  exact transcriptWin_mono _ _ _ (memoize_log_sublist _ ∅ logs hlogs) verified

theorem prob_sourceGame_le_memo (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) :
    Pr[= true | evaluateSource sign (sourceGame publicKey adversary) cache] ≤
      Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache] := by
  unfold evaluateSource
  rw [probOutput_congr rfl (evalDist_runSigning_memoize sign (sourceGame publicKey adversary) cache)]
  change Pr[= true | evaluateSource sign (memoize (sourceGame publicKey adversary) ∅) cache] ≤
    Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, evaluateSource_map, evaluateSource_map]
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  exact transcriptReduction_win publicKey adversary result (evaluateSource_support sign _ cache hresult) hwin

theorem prob_tableGameAfterSecrets_le_memo (adversary : Adversary) (parameter : PublicParameter)
    (outputs : ChainSecrets) (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ romImpl (tableGameAfterSecrets adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ romImpl (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterSecrets
  rw [run'_lift_hash_bind, run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem prob_independentTableGame_le_memo (adversary : Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterSecrets_le_memo _ _ _ _ ∅

theorem freshRequests_sourceGame_memo (publicKey : PublicKey) (adversary : Adversary) :
    FreshRequests ∅ (sourceGame publicKey (memoAdversary adversary)) := by
  have h : FreshRequests ∅ (memoize (adversary.main publicKey) ∅) := by
    simpa only [QueryCache.empty_apply, ne_eq, not_true_eq_false, Set.setOf_false] using
      freshRequests_memoize (adversary.main publicKey) ∅
  unfold sourceGame memoAdversary
  apply h.withRequestLog.bind
  intro result used
  rw [← bind_pure (baseLift (finishGame publicKey result))]
  exact freshRequests_base_bind used (finishGame publicKey result) _ (fun value => .pure value)

/-- info: 'XmssSecurity.EUFCMA.Seeded.prob_independentTableGame_le_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prob_independentTableGame_le_memo

end XmssSecurity.EUFCMA.Seeded

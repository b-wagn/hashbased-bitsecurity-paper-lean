import XmssSecurity.Proof.TargetSum.EUFCMA.SeededTable
import XmssSecurity.Proof.Generic.Deterministic.MemoTable
import XmssSecurity.Proof.Generic.Deterministic.RequestSampling
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Memoizing repeated signing inputs preserves standard winning executions.
The standard freshness predicate is monotone when the forwarded log is shortened. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded Generic.DeterministicSigning

set_option backward.isDefEq.respectTransparency false

def transcriptWin (forgery : Generic.Forgery) (log : QueryLog Generic.SigningSpec) (verified : Bool) : Bool :=
  decide (SUFCMA.SigningTranscript.Valid log ∧ ¬EUFCMA.SigningTranscript.ContainsRequest log forgery) && verified

theorem transcriptWin_mono (forgery : Generic.Forgery) (original forwarded : QueryLog Generic.SigningSpec)
    (h : forwarded.Sublist original) (verified : Bool) (hwin : transcriptWin forgery original verified = true) :
    transcriptWin forgery forwarded verified = true := by
  simp only [transcriptWin, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  refine ⟨⟨List.Nodup.sublist (h.map _) hwin.1.1, ?_⟩, hwin.2⟩
  rintro ⟨entry, hentry, heq⟩
  exact hwin.1.2 ⟨entry, h.subset hentry, heq⟩

noncomputable def finishGame (publicKey : PublicKey) (result : Generic.Forgery × QueryLog Generic.SigningSpec) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (Generic.Concrete.verify publicKey result.1.epoch result.1.message result.1.signature : OracleComp HashSpec Bool)
  return transcriptWin result.1 result.2 verified

noncomputable def sourceGame (publicKey : PublicKey) (adversary : Generic.Adversary) :
    OracleComp (OracleWorld + Generic.SigningSpec) Bool :=
  Generic.DeterministicSigning.withRequestLog (adversary.main publicKey) >>= fun result => Generic.DeterministicSigning.baseLift (finishGame publicKey result)

noncomputable def transcriptReduction (publicKey : PublicKey) (adversary : Generic.Adversary) :
    OracleComp (OracleWorld + Generic.SigningSpec) (Bool × Bool) := do
  let result ← Generic.DeterministicSigning.withRequestLog (Generic.DeterministicSigning.memoize (Generic.DeterministicSigning.withRequestLog (adversary.main publicKey)) ∅)
  let verified ← Generic.DeterministicSigning.baseLift (liftM
    (Generic.Concrete.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return (transcriptWin result.1.1 result.1.2 verified, transcriptWin result.1.1 result.2 verified)

theorem runSigning_sourceGame (randomizers : Generic.Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (publicKey : PublicKey) (adversary : Generic.Adversary) :
    Generic.Seeded.runSigning (fun (request : Generic.SignRequest) => Generic.Seeded.tableSign randomizers secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest (Generic.Seeded.tableScheme randomizers) adversary publicKey secretKey := by
  simp only [sourceGame, Generic.Seeded.runSigning, simulateQ_bind, Generic.DeterministicSigning.simulateQ_baseLift, simulateQ_ofLift_eq_self]
  rw [show simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
      fun (request : Generic.SignRequest) => liftM (Generic.Seeded.tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Generic.Signature)))
      (Generic.DeterministicSigning.withRequestLog (adversary.main publicKey)) =
        Generic.Seeded.loggedRun (fun (request : Generic.SignRequest) => liftM (Generic.Seeded.tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Generic.Signature)))
          (adversary.main publicKey) from Generic.Seeded.runSigning_withRequestLog _ _]
  unfold Generic.Seeded.loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem fst_transcriptReduction (publicKey : PublicKey) (adversary : Generic.Adversary) :
    Prod.fst <$> transcriptReduction publicKey adversary = Generic.DeterministicSigning.memoize (sourceGame publicKey adversary) ∅ := by
  unfold transcriptReduction sourceGame
  rw [Generic.DeterministicSigning.memoize_baseLift_bind]
  conv_rhs => rw [← Generic.DeterministicSigning.fst_withRequestLog (Generic.DeterministicSigning.memoize (Generic.DeterministicSigning.withRequestLog (adversary.main publicKey)) ∅)]
  simp only [map_bind, bind_map_left, map_pure, finishGame, Generic.DeterministicSigning.baseLift, simulateQ_bind, simulateQ_pure]

theorem snd_transcriptReduction (publicKey : PublicKey) (adversary : Generic.Adversary) :
    Prod.snd <$> transcriptReduction publicKey adversary = sourceGame publicKey (Generic.Seeded.memoAdversary adversary) := by
  unfold transcriptReduction sourceGame Generic.Seeded.memoAdversary
  rw [← Generic.DeterministicSigning.withRequestLog_memoize_forget (adversary.main publicKey) ∅]
  simp only [map_bind, bind_map_left, map_pure, finishGame, Generic.DeterministicSigning.baseLift, simulateQ_bind, simulateQ_pure]

theorem transcriptReduction_win (publicKey : PublicKey) (adversary : Generic.Adversary)
    (result : Bool × Bool) (hresult : result ∈ support (transcriptReduction publicKey adversary)) :
    result.1 = true → result.2 = true := by
  simp only [transcriptReduction, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨logs, hlogs, verified, _, rfl⟩ := hresult
  exact transcriptWin_mono _ _ _ (Generic.DeterministicSigning.memoize_log_sublist _ ∅ logs hlogs) verified

theorem prob_sourceGame_le_memo (sign : Generic.SignRequest → OracleComp HashSpec (Option Generic.Signature))
    (publicKey : PublicKey) (adversary : Generic.Adversary) (cache : QueryCache HashSpec) :
    Pr[= true | Generic.Seeded.evaluateSource sign (sourceGame publicKey adversary) cache] ≤
      Pr[= true | Generic.Seeded.evaluateSource sign (sourceGame publicKey (Generic.Seeded.memoAdversary adversary)) cache] := by
  unfold Generic.Seeded.evaluateSource
  rw [probOutput_congr rfl (Generic.Seeded.evalDist_runSigning_memoize sign (sourceGame publicKey adversary) cache)]
  change Pr[= true | Generic.Seeded.evaluateSource sign (Generic.DeterministicSigning.memoize (sourceGame publicKey adversary) ∅) cache] ≤
    Pr[= true | Generic.Seeded.evaluateSource sign (sourceGame publicKey (Generic.Seeded.memoAdversary adversary)) cache]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, Generic.Seeded.evaluateSource_map, Generic.Seeded.evaluateSource_map]
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  exact transcriptReduction_win publicKey adversary result (Generic.Seeded.evaluateSource_support sign _ cache hresult) hwin

theorem prob_tableGameAfterSecrets_le_memo (adversary : Generic.Adversary) (parameter : PublicParameter)
    (outputs : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ Generic.romImpl (tableGameAfterSecrets adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ Generic.romImpl (tableGameAfterSecrets (Generic.Seeded.memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterSecrets
  rw [Generic.Seeded.run'_lift_hash_bind, Generic.Seeded.run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem prob_independentTableGame_le_memo (adversary : Generic.Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (Generic.Seeded.memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterSecrets_le_memo _ _ _ _ ∅

theorem freshRequests_sourceGame_memo (publicKey : PublicKey) (adversary : Generic.Adversary) :
    Generic.DeterministicSigning.FreshRequests ∅ (sourceGame publicKey (Generic.Seeded.memoAdversary adversary)) := by
  have h : Generic.DeterministicSigning.FreshRequests ∅ (Generic.DeterministicSigning.memoize (adversary.main publicKey) ∅) := by
    simpa only [QueryCache.empty_apply, ne_eq, not_true_eq_false, Set.setOf_false] using
      Generic.DeterministicSigning.freshRequests_memoize (adversary.main publicKey) ∅
  unfold sourceGame Generic.Seeded.memoAdversary
  apply h.withRequestLog.bind
  intro result used
  rw [← bind_pure (Generic.DeterministicSigning.baseLift (finishGame publicKey result))]
  exact Generic.DeterministicSigning.freshRequests_base_bind used (finishGame publicKey result) _ (fun value => .pure value)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.prob_independentTableGame_le_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prob_independentTableGame_le_memo

end XmssSecurity.TargetSum.EUFCMA.Seeded

import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayFallback
import XmssSecurity.Proof.TargetSum.EUFCMA.Execution
import XmssSecurity.Proof.TargetSum.Attack.NeighborSeeded

/-! The one-request, one-probe adversary implementing the replay/fallback
experiment. Both possible output messages are fresh in the standard game. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Attack

def replayRequest : SignRequest := mutationRequest

def replayCandidate : Message := 1

def replayFallbackMessage : Message := 2

noncomputable def replaySelectedMessage (output : HashOutput) : Message :=
  if TargetSum.ValidDigest (truncateHash output) then replayCandidate else replayFallbackMessage

theorem replaySelectedMessage_fresh (output : HashOutput) :
    replaySelectedMessage output ≠ replayRequest.message := by
  unfold replaySelectedMessage
  split <;> decide

noncomputable def replayAfterSigning (publicKey : PublicKey) (answer : Option Signature) :
    OracleComp OracleWorld Forgery := do
  let original := answer.getD fallbackSignature
  let output ← liftM (OracleWorld.query (.inr (CacheView.encodingInput publicKey.parameter
    replayRequest.epoch (replayCandidate, original.randomness))))
  return ⟨replayRequest.epoch, replaySelectedMessage output, original⟩

noncomputable def replayMain (publicKey : PublicKey) : OracleComp (OracleWorld + SigningSpec) Forgery := do
  let answer ← liftM ((OracleWorld + SigningSpec).query (.inr replayRequest))
  liftWorldToAdversary (replayAfterSigning publicKey answer)

noncomputable def replayAdversary : XmssSecurity.TargetSum.Adversary := ⟨replayMain⟩

noncomputable def replayStatementAdversary : SUFCMA.Adversary OracleWorld PublicKey Message Signature lifetime :=
  ⟨replayMain⟩

theorem replayAfterSigning_fresh (publicKey : PublicKey) (answer : Option Signature)
    (forgery : Forgery) (hmem : forgery ∈ support (replayAfterSigning publicKey answer)) :
    forgery.message ≠ replayRequest.message := by
  simp only [replayAfterSigning, bind_pure_comp, support_map, Set.mem_image] at hmem
  obtain ⟨output, _, rfl⟩ := hmem
  exact replaySelectedMessage_fresh output

theorem replayAfterSigning_noSeed (publicKey : PublicKey) (answer : Option Signature) :
    (replayAfterSigning publicKey answer).IsQueryBoundP (XmssSecurity.TargetSum.Seeded.hashBad MaySeedHit) 0 := by
  simp [replayAfterSigning, XmssSecurity.TargetSum.Seeded.hashBad, CacheView.encodingInput,
    not_maySeedHit_tweakableHashInput]

theorem replayMain_logged {Key : Type} (scheme : Scheme Key) (secretKey : Key) (publicKey : PublicKey) :
    (simulateQ (forwardOracles + signingOracle scheme secretKey) (replayMain publicKey)).run = (do
      let answer ← scheme.sign secretKey replayRequest.epoch replayRequest.message
      let forgery ← replayAfterSigning publicKey answer
      return (forgery, [⟨replayRequest, answer⟩])) := by
  unfold replayMain
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  have hsign : (signingOracle scheme secretKey replayRequest).run =
      (scheme.sign secretKey replayRequest.epoch replayRequest.message >>= fun answer =>
        pure (answer, [⟨replayRequest, answer⟩])) := QueryImpl.run_withLogging_apply _ _
  simp only [QueryImpl.add_apply_inr, hsign, bind_map_left, liftWorldToAdversary_logged,
    bind_pure_comp, Functor.map_map, List.append_nil]

theorem replay_gameRest {Key : Type} (scheme : Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    gameRest scheme replayAdversary publicKey secretKey = (do
      let answer ← scheme.sign secretKey replayRequest.epoch replayRequest.message
      let forgery ← replayAfterSigning publicKey answer
      scheme.verify publicKey forgery.epoch forgery.message forgery.signature) := by
  unfold gameRest
  change (do
    let result ← (simulateQ (forwardOracles + signingOracle scheme secretKey) (replayMain publicKey)).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (SigningTranscript.Valid result.2 ∧ ¬ SigningTranscript.ContainsRequest result.2 result.1) && verified) = _
  rw [replayMain_logged]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro answer
  apply bind_congr_of_forall_mem_support
  intro forgery hmem
  have hfresh := replayAfterSigning_fresh publicKey answer forgery hmem
  have hnot : ¬ SigningTranscript.ContainsRequest [⟨replayRequest, answer⟩] forgery := by
    simp only [SigningTranscript.ContainsRequest, List.mem_singleton, exists_eq_left]
    intro heq
    exact hfresh (congrArg (fun request : SignRequest => request.message) heq).symm
  simp only [hnot, not_false_eq_true, and_true,
    show SigningTranscript.Valid [⟨replayRequest, answer⟩] from by simp [SUFCMA.SigningTranscript.Valid],
    decide_true, Bool.true_and, bind_pure]

theorem replay_strong_gameRest {Key : Type} (scheme : Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    XmssSecurity.TargetSum.Seeded.gameRest scheme replayAdversary publicKey secretKey =
      gameRest scheme replayAdversary publicKey secretKey := by
  rw [replay_gameRest]
  unfold XmssSecurity.TargetSum.Seeded.gameRest
  change (do
    let result ← (simulateQ (forwardOracles + signingOracle scheme secretKey) (replayMain publicKey)).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified) = _
  rw [replayMain_logged]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro answer
  apply bind_congr_of_forall_mem_support
  intro forgery hmem
  have hfresh := replayAfterSigning_fresh publicKey answer forgery hmem
  have hnot : ¬SigningTranscript.Contains [⟨replayRequest, answer⟩] forgery := by
    simp only [SUFCMA.SigningTranscript.Contains, List.mem_singleton, exists_eq_left, not_and]
    intro heq _
    exact hfresh (congrArg (fun request : SignRequest => request.message) heq).symm
  simp only [hnot, not_false_eq_true, and_true,
    show SigningTranscript.Valid [⟨replayRequest, answer⟩] from by simp [SUFCMA.SigningTranscript.Valid],
    decide_true, Bool.true_and, bind_pure]

theorem replayMain_counted (publicKey : PublicKey) :
    QueryCounting.counted Direct.IsDirectHashQuery (replayMain publicKey) =
      (fun forgery => (forgery, 1)) <$> replayMain publicKey := by
  unfold replayMain replayAfterSigning liftWorldToAdversary
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    QueryCounting.counted_query_bind, QueryCounting.counted_pure,
    map_bind, map_pure, pure_bind, Direct.not_isDirectHashQuery_sign,
    Direct.isDirectHashQuery_hash, if_false, if_true, Nat.add_zero, Nat.zero_add,
    Prod.mk.eta, bind_pure]
  rfl

end XmssSecurity.TargetSum.EUFCMA

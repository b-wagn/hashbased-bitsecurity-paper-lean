import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsBasic
import XmssSecurity.Proof.TargetSum.EUFCMA.DirectBridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The direct-plus-requests statement has exactly the shared counter used by
the syntactic proof. Pruning therefore preserves the standard game, including
its signing log and freshness condition. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

abbrev mode : SUFCMA.CountingMode := ⟨false, false, false, true⟩

attribute [local irreducible] Generic.sampleMasterSeed

theorem signingOracleCounted_request
    (secretKey : Generic.Seeded.SecretKey) (request : SignRequest) :
    SUFCMA.signingOracleCounted (fun _ => 0) 1 Generic.xmss secretKey request =
      ((SUFCMA.signingOracle Generic.xmss secretKey).withAddCost (fun _ => 1)) request := by
  refine WriterT.ext _ _ ?_
  refine WriterT.ext _ _ ?_
  simp only [SUFCMA.signingOracleCounted, Modes.charge_zero, SUFCMA.signingOracle,
    QueryImpl.withLogging_apply, QueryImpl.withAddCost_apply, WriterT.run_bind,
    Modes.run_liftM_chargedRun, Modes.run_liftM_chargedRun', Modes.run_liftM_logged,
    WriterT.run_tell, WriterT.run_pure, add_zero, map_bind, bind_map_left,
    Functor.map_map, pure_bind, map_pure, one_mul, mul_one,
    LawfulAppend.empty_append, LawfulAppend.append_empty, AddWriterT.addTell]

theorem impl_requests_eq (secretKey : Generic.Seeded.SecretKey) :
    (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
        (RandomOracleModel.hashCost HashInput HashOutput) +
      SUFCMA.signingOracleCounted (fun _ => 0) 1 Generic.xmss secretKey =
    (Security.adversaryImpl secretKey).withAddCost (fun input => if IsCharged input then 1 else 0) := by
  funext input
  rcases input with (sample | hashInput) | request
  · rfl
  · rfl
  · simpa only [QueryImpl.add_apply_inr, QueryImpl.withAddCost_apply,
      Security.adversaryImpl, charged_sign, if_true] using signingOracleCounted_request secretKey request

theorem gameCounted_eq (adversary : Security.StatementAdversary) :
    gameCounted mode (RandomOracleModel.hashCost HashInput HashOutput) Generic.xmss adversary = (do
      let (publicKey, secretKey) ← Generic.xmss.keygen
      let ((forgery, charged), log) ← (simulateQ (Security.adversaryImpl secretKey)
        (QueryCounting.counted IsCharged (adversary.main publicKey))).run
      let verified ← Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature
      pure (decide (SUFCMA.SigningTranscript.Valid log ∧
        ¬SigningTranscript.ContainsRequest log forgery) && verified, charged)) := by
  unfold gameCounted
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true,
    Modes.charge_zero, impl_requests_eq, bind_map_left]
  apply bind_congr
  rintro ⟨publicKey, secretKey⟩
  rw [← QueryCounting.simulate_withCost]
  apply bind_congr
  rintro ⟨⟨forgery, charged⟩, log⟩
  simp only [zero_add, add_zero]
  rfl

theorem adversary_counted_bound (adversary : Security.StatementAdversary) (q : ℕ)
    (hbound : (notion mode).HasQueryBound Generic.xmss adversary q)
    (publicKey : PublicKey) (secretKey : Generic.Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkey : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl Generic.xmss.keygen).run ∅))
    (forgery : Forgery) (charged : ℕ) (log : QueryLog SigningSpec) (cache' : QueryCache HashSpec)
    (hresult : (((forgery, charged), log), cache') ∈ support ((simulateQ romImpl
      (simulateQ (Security.adversaryImpl secretKey)
        (QueryCounting.counted IsCharged (adversary.main publicKey))).run).run cache)) :
    charged ≤ q := by
  obtain ⟨verification, hverification⟩ := probComp_support_nonempty
    ((simulateQ romImpl (Generic.xmss.verify publicKey forgery.epoch forgery.message forgery.signature)).run cache')
  refine hbound (decide (SUFCMA.SigningTranscript.Valid log ∧
    ¬SigningTranscript.ContainsRequest log forgery) && verification.1, charged) ?_
  simp only [notion, RandomOracleModel.run]
  rw [gameCounted_eq, ← Security.romImpl_eq, StateT.run'_eq, support_map]
  refine ⟨((decide (SUFCMA.SigningTranscript.Valid log ∧
    ¬SigningTranscript.ContainsRequest log forgery) && verification.1, charged), verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind]
  rw [mem_support_bind_iff]
  refine ⟨((publicKey, secretKey), cache), hkey, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨(((forgery, charged), log), cache'), hresult, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨verification, hverification, by simp⟩

theorem forgeAdvantage_prune_eq (adversary : Security.StatementAdversary) (q : ℕ)
    (hbound : (notion mode).HasQueryBound Generic.xmss adversary q) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) =
      forgeAdvantage Seeded.scheme (pruneAdversary q (Security.embed adversary)) := by
  unfold forgeAdvantage
  refine congrArg (fun computation => Pr[= true | computation]) ?_
  unfold gameCore
  simp only [simulateQ_bind, StateT.run'_bind']
  refine bind_congr_of_forall_mem_support _ fun keys hkeys => ?_
  rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
  dsimp only
  unfold gameRest
  simp only [simulateQ_bind, StateT.run'_bind']
  have hprune := simulate_prune_eq_logged (Security.adversaryImpl secretKey)
    (adversary.main publicKey) q cache
    (fun result hresult => by
      rcases result with ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩
      exact adversary_counted_bound adversary q hbound publicKey secretKey cache hkeys
        forgery charged log cache' hresult)
  exact congrArg (fun computation => computation >>= _) hprune.symm

theorem security_of_isQueryBound (bits : ℕ)
    (h : ∀ (adversary : Adversary) (q : ℕ), 1 ≤ q → IsQueryBound adversary q →
      forgeAdvantage Seeded.scheme adversary ≤ q / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion mode).HasClassicalSecurityBits Generic.xmss bits := by
  intro q hq adversary hbound
  rw [notion_advantage_eq, forgeAdvantage_prune_eq adversary q hbound]
  exact h _ q hq (pruneAdversary_isQueryBound q (Security.embed adversary))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.security_of_isQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms security_of_isQueryBound

end XmssSecurity.TargetSum.EUFCMA.Requests

import XmssSecurity.Proof.Attack.ChainMutation
import XmssSecurity.Proof.Modes.Projection
import XmssSecurity.Statement.Claims

/-! The mutation adversary has budget one in the statement's counted experiment. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity

namespace Modes

open SUFCMA

variable {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}

theorem signingOracleCounted_requests (scheme : SynchronizedSignature spec PK SK Msg Sig L)
    (sk : SK) (requestCost : ℕ) (request : SUFCMA.SignRequest Msg L) :
    signingOracleCounted (fun _ => 0) requestCost scheme sk request =
      ((SUFCMA.signingOracle scheme sk).withAddCost (fun _ => requestCost)) request := by
  refine WriterT.ext _ _ ?_
  simp only [signingOracleCounted, charge_zero, SUFCMA.signingOracle, QueryImpl.withLogging_apply,
    QueryImpl.withAddCost_apply]
  refine WriterT.ext _ _ ?_
  simp only [WriterT.run_bind, run_liftM_chargedRun, run_liftM_chargedRun', run_liftM_logged,
    WriterT.run_tell, WriterT.run_pure, add_zero, map_bind, bind_map_left,
    Functor.map_map, pure_bind, map_pure, one_mul, mul_one, LawfulAppend.empty_append,
    LawfulAppend.append_empty, AddWriterT.addTell]

theorem impl_requests_eq (cost : spec.Domain → ℕ)
    (scheme : SynchronizedSignature spec PK SK Msg Sig L) (sk : SK) :
    (QueryImpl.ofLift spec
        (WriterT (QueryLog (SUFCMA.SigningSpec Msg Sig L)) (OracleComp spec))).withAddCost cost +
      signingOracleCounted (fun _ => 0) 1 scheme sk =
    (QueryImpl.ofLift spec (WriterT (QueryLog (SUFCMA.SigningSpec Msg Sig L)) (OracleComp spec)) +
        SUFCMA.signingOracle scheme sk).withAddCost (fun | .inl input => cost input | .inr _ => 1) := by
  funext input
  cases input with
  | inl input => simp only [QueryImpl.add_apply_inl, QueryImpl.withAddCost_apply]
  | inr request => simp only [QueryImpl.add_apply_inr, signingOracleCounted_requests,
      QueryImpl.withAddCost_apply]

end Modes

namespace Attack

attribute [local irreducible] sampleMasterSeed

theorem chainMutation_gameCounted_requests :
    SUFCMA.gameCounted ⟨false, false, false, true⟩
        (RandomOracleModel.hashCost HashInput HashOutput) xmss chainMutationSufCmaAdversary =
      (fun result => (result, 1)) <$> SUFCMA.game xmss chainMutationSufCmaAdversary := by
  unfold SUFCMA.gameCounted SUFCMA.game
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero,
    bind_map_left, map_bind, map_pure, zero_add, add_zero]
  apply bind_congr
  intro keys
  rcases keys with ⟨publicKey, secretKey⟩
  have himpl := (Modes.impl_requests_eq (RandomOracleModel.hashCost HashInput HashOutput)
    xmss secretKey).trans (congrArg
      (fun cost => (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          SUFCMA.signingOracle xmss secretKey).withAddCost cost)
      (show _ = (fun input => if IsHashOrRequest input then 1 else 0) from by
        funext input
        rcases input with (uniformOrHash | request)
        · rcases uniformOrHash <;> rfl
        · rfl))
  rw [himpl, ← QueryCounting.simulate_withCost, show chainMutationSufCmaAdversary.main publicKey =
    chainMutationMain from rfl, chainMutation_counted]
  simp only [simulateQ_map, WriterT.run_map', bind_map_left]
  rfl

theorem chainMutation_experiment_requests :
    (SUFCMA.notion ⟨false, false, false, true⟩).experiment xmss chainMutationSufCmaAdversary =
      (fun result => (result, 1)) <$>
        RandomOracleModel.run (SUFCMA.game xmss chainMutationSufCmaAdversary) := by
  simp only [SUFCMA.notion, chainMutation_gameCounted_requests, RandomOracleModel.run,
    simulateQ_map, StateT.run'_map']

theorem chainMutation_requests_queryBound :
    (SUFCMA.notion ⟨false, false, false, true⟩).HasQueryBound xmss
      chainMutationSufCmaAdversary 1 := by
  intro result hresult
  rw [chainMutation_experiment_requests, support_map] at hresult
  obtain ⟨won, _, rfl⟩ := hresult
  exact le_rfl

theorem chainMutation_requests_advantage :
    (SUFCMA.notion ⟨false, false, false, true⟩).advantage xmss chainMutationSufCmaAdversary =
      forgeAdvantage Seeded.scheme chainMutationAdversary := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  rfl

theorem requests_attack_of_chainMutation_advantage
    (hadvantage : (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      forgeAdvantage Seeded.scheme chainMutationAdversary) :
    XmssSufCmaAttack ⟨false, false, false, true⟩ 122 := by
  intro hsecure
  have hbound := hsecure 1 le_rfl chainMutationSufCmaAdversary chainMutation_requests_queryBound
  rw [chainMutation_requests_advantage, Nat.cast_one] at hbound
  exact (not_lt_of_ge hbound) hadvantage

/-- info: 'XmssSecurity.Attack.chainMutation_requests_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_requests_queryBound

end Attack

end XmssSecurity

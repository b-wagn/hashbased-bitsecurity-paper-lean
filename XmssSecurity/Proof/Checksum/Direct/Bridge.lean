import XmssSecurity.Proof.Checksum.Direct.Prune
import XmssSecurity.Proof.Checksum.Adversary.Embedding

/-!
# From the direct-count statement to a syntactically bounded adversary

`SUFCMA.notionDirect xmss` charges an adversary for its own hash queries, on every execution of
the experiment. This file turns that semantic bound into the syntactic bound `IsDirectQueryBound`
of the proof: an adversary whose executions never exceed `D` direct hash queries wins the game
with exactly the same probability as its pruning after `D` queries (`pruneAdversary`), which is
syntactically bounded.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Security

open Direct

set_option backward.isDefEq.respectTransparency false

-- Unfolding the master-seed sampler enumerates `2^256` seeds; keep it opaque.
attribute [local irreducible] sampleMasterSeed

theorem romImpl_eq : romImpl = RandomOracleModel.impl HashInput HashOutput := rfl

/-- Forgetting the cost layer of a counted simulation under a logged implementation. -/
theorem map_fst_run_run_withAddCost {ι : Type} {spec : OracleSpec ι} {ι' : Type}
    {spec' : OracleSpec ι'} {τ α : Type}
    (impl : QueryImpl spec (WriterT (List τ) (OracleComp spec'))) (cost : spec.Domain → ℕ)
    (computation : OracleComp spec α) :
    Prod.map Prod.fst id <$> (simulateQ (impl.withAddCost cost) computation).run.run =
      (simulateQ impl computation).run := by
  have h := QueryImpl.fst_map_run_withCost impl (fun t => Multiplicative.ofAdd (cost t)) computation
  rw [← h, WriterT.run_map']
  rfl

/-- A counted simulation followed by a continuation ignoring the count is the plain simulation
followed by the continuation. -/
theorem bind_map_fst_eq {ι : Type} {spec : OracleSpec ι} {ι' : Type}
    {spec' : OracleSpec ι'} {τ α β : Type}
    (impl : QueryImpl spec (WriterT (List τ) (OracleComp spec'))) (cost : spec.Domain → ℕ)
    (computation : OracleComp spec α) (continuation : α × List τ → OracleComp spec' β) :
    ((simulateQ (impl.withAddCost cost) computation).run.run >>=
      fun result => continuation (result.1.1, result.2)) =
    (simulateQ impl computation).run >>= continuation := by
  rw [← map_fst_run_run_withAddCost impl cost computation, map_eq_bind_pure_comp (OracleComp spec')]
  simp only [bind_assoc, Function.comp_apply, pure_bind]
  rfl

/-- The counted game projects to the game. -/
theorem gameCounted_map_fst {ι : Type} {spec : OracleSpec ι} {PK SK Msg Sig : Type} {L : ℕ}
    [DecidableEq Msg] [DecidableEq Sig] (cost : spec.Domain → ℕ)
    (scheme : EpochBasedSignature spec PK SK Msg Sig L)
    (adversary : SUFCMA.Adversary spec PK Msg Sig L) :
    Prod.fst <$> SUFCMA.gameCountedDirect cost scheme adversary = SUFCMA.game scheme adversary := by
  unfold SUFCMA.gameCountedDirect SUFCMA.game
  simp only [map_bind, map_pure]
  refine bind_congr fun keys => ?_
  rcases keys with ⟨publicKey, secretKey⟩
  dsimp only
  exact bind_map_fst_eq _ _ _ (fun result => do
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    pure (decide (SigningTranscript.Valid result.2 ∧
      ¬SigningTranscript.Contains result.2 result.1) && verified))

/-- The direct-count advantage of a statement adversary is the proof's success probability. -/
theorem notionDirect_advantage_eq (adversary : StatementAdversary) :
    SUFCMA.notionDirect.advantage xmss adversary =
      forgeAdvantage Seeded.scheme (embed adversary) := by
  simp only [SecurityNotion.advantage, SUFCMA.notionDirect, RandomOracleModel.run]
  unfold forgeAdvantage
  rw [game_embed, ← gameCounted_map_fst, ← romImpl_eq, simulateQ_map,
    StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  rfl

/-- A cost layer charging exactly the direct hash queries is the syntactic counter. -/
theorem run_withAddCost_eq_counted {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (cost : (OracleWorld + SigningSpec).Domain → ℕ)
    (hcost : ∀ input, cost input = if IsDirectHashQuery input then 1 else 0)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ (impl.withAddCost cost) computation).run =
      simulateQ impl (QueryCounting.counted IsDirectHashQuery computation) := by
  have hfun : cost = fun input => if IsDirectHashQuery input then 1 else 0 := funext hcost
  subst hfun
  exact (QueryCounting.simulate_withCost IsDirectHashQuery impl computation).symm

/-- The implementation the statement's game runs the adversary under, in the proof's names. -/
@[reducible] noncomputable def adversaryImpl (secretKey : Seeded.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
    SUFCMA.signingOracle xmss secretKey

/-- Every execution of the adversary part, after any reachable key generation, stays within the
statement's query bound. -/
theorem adversary_counted_bound (adversary : StatementAdversary) (D : ℕ)
    (hD : SUFCMA.notionDirect.HasQueryBound xmss adversary D)
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkeys : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl xmss.keygen).run ∅))
    (forgery : Forgery) (charged : ℕ) (log : QueryLog SigningSpec) (cache' : QueryCache HashSpec)
    (hresult : (((forgery, charged), log), cache') ∈ support ((simulateQ romImpl
      (simulateQ (adversaryImpl secretKey)
        (QueryCounting.counted IsDirectHashQuery (adversary.main publicKey))).run).run cache)) :
    charged ≤ D := by
  obtain ⟨verification, hverification⟩ := probComp_support_nonempty
    ((simulateQ romImpl (xmss.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run cache')
  refine hD (decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log forgery) && verification.1, charged) ?_
  simp only [SUFCMA.notionDirect, RandomOracleModel.run]
  rw [← romImpl_eq]
  unfold SUFCMA.gameCountedDirect
  rw [StateT.run'_eq, support_map]
  refine ⟨((decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log forgery) && verification.1, charged),
    verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind]
  rw [mem_support_bind_iff]
  refine ⟨((publicKey, secretKey), cache), hkeys, ?_⟩
  dsimp only
  rw [mem_support_bind_iff]
  refine ⟨(((forgery, Multiplicative.ofAdd charged), log), cache'), ?_, ?_⟩
  · rw [run_withAddCost_eq_counted _ _ (fun input => by
      rcases input with (uniformOrHash | request)
      · rcases uniformOrHash with n | hashInput <;> rfl
      · rfl)]
    exact hresult
  dsimp only
  rw [mem_support_bind_iff]
  exact ⟨verification, hverification, by simp⟩

/-- Pruning after the statement's bound does not change the success probability. -/
theorem forgeAdvantage_prune_eq (adversary : StatementAdversary) (D : ℕ)
    (hD : SUFCMA.notionDirect.HasQueryBound xmss adversary D) :
    forgeAdvantage Seeded.scheme (embed adversary) =
      forgeAdvantage Seeded.scheme (pruneAdversary D (embed adversary)) := by
  unfold forgeAdvantage
  refine congrArg (fun computation => Pr[= true | computation]) ?_
  unfold gameCore
  simp only [simulateQ_bind, StateT.run'_bind']
  refine bind_congr_of_forall_mem_support _ fun keys hkeys => ?_
  rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
  dsimp only
  unfold Seeded.gameRest
  simp only [simulateQ_bind, StateT.run'_bind']
  have hprune := simulateQ_pruneDirect_eq_logged (adversaryImpl secretKey)
    (adversary.main publicKey) D cache
    (fun result hresult => by
      rcases result with ⟨⟨⟨forgery, charged⟩, log⟩, cache'⟩
      exact adversary_counted_bound adversary D hD publicKey secretKey cache hkeys
        forgery charged log cache' hresult)
  exact congrArg (fun computation => computation >>= _) hprune.symm

/-- The statement's direct-count claim follows from a bound for syntactically bounded
adversaries of the proof. -/
theorem sufCmaDirect_of_isDirectQueryBound (bits : ℕ)
    (h : ∀ (adversary : Adversary) (D : ℕ), 1 ≤ D → IsDirectQueryBound adversary D →
      forgeAdvantage Seeded.scheme adversary ≤ D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    SUFCMA.notionDirect.HasClassicalSecurityBits xmss bits := by
  intro D hD adversary hbound
  rw [notionDirect_advantage_eq, forgeAdvantage_prune_eq adversary D hbound]
  exact h _ D hD (pruneAdversary_isDirectQueryBound D (embed adversary))

end XmssSecurity.Checksum.Security

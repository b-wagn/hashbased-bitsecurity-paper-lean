import XmssSecurity.Proof.Attack.NeighborAccounting
import XmssSecurity.Proof.NoSign.WeightedPrune
import XmssSecurity.Proof.NoSign.Concrete
import XmssSecurity.Proof.Direct.Bridge
import XmssSecurity.Proof.Direct.SeedGuessing
import XmssSecurity.Proof.Modes.Projection

/-!
# Small budgets in the signer modes

When the signer's hash calls are charged, a signing request costs its two signer hashes, and
one more unit when the requests are charged. Every execution of the adversary within the
statement's budget `q` is an execution of its pruning at the weighted budget
(`forgeAdvantage_pruneWeighted_eq`); below the cost of a request, the pruned adversary makes no
request, and the no-signature bound applies (`signer_small_advantage_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.NoSign

attribute [local irreducible] sampleMasterSeed

/-- The signer makes exactly two hash queries, the randomizer and the encoding. -/
theorem countHashQueries_xmss_sign (secretKey : Seeded.SecretKey) (leafIndex : LeafIndex)
    (message : Message) :
    countHashQueries (xmss.sign secretKey leafIndex message) =
      (fun answer => (answer, 2)) <$> xmss.sign secretKey leafIndex message := by
  change countHashQueries (liftComp (Seeded.sign secretKey leafIndex message :
      OracleComp HashSpec (Option Signature)) OracleWorld) =
    (fun answer => (answer, 2)) <$> liftComp (Seeded.sign secretKey leafIndex message :
      OracleComp HashSpec (Option Signature)) OracleWorld
  have hlift : ∀ input : HashInput,
      (liftComp (liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput)
        OracleWorld : OracleComp OracleWorld HashOutput) = liftM (OracleWorld.query (.inr input)) :=
    fun _ => rfl
  have hsingle : ∀ input : HashInput,
      countHashQueries (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput) =
        (fun output => (output, 1)) <$> liftM (OracleWorld.query (.inr input)) := by
    intro input
    unfold countHashQueries
    rw [← bind_pure (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput),
      QueryCounting.counted_query_bind]
    simp [QueryCounting.counted_pure]
  simp only [countHashQueries] at hsingle
  simp only [Seeded.sign, deriveRandomizer, Concrete.encodingHash, Concrete.tweakableHash,
    Concrete.oracleHash, HasQuery.query, liftComp_bind, liftComp_map, liftComp_bind_pure,
    liftComp_pure, bind_pure_comp, hlift]
  simp only [countHashQueries, QueryCounting.counted_bind, QueryCounting.counted_map, hsingle,
    map_bind, bind_map_left, Functor.map_map]
  simp only [bind_pure_comp]
  rfl

/-- The statement's counted run of the adversary in a signer mode, from the logged run with the
direct hash queries counted: each request costs `requestCost` and the signer's two hashes. -/
theorem statementCountedRun_eq {α : Type} (secretKey : Seeded.SecretKey) (requestCost : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    (simulateQ
      ((QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
          (RandomOracleModel.hashCost HashInput HashOutput) +
        SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput)
          requestCost xmss secretKey) computation).run.run =
      (fun result : (α × ℕ) × QueryLog SigningSpec =>
        ((result.1.1, Multiplicative.ofAdd (result.1.2 + (requestCost + 2) * result.2.length)),
          result.2)) <$>
        (simulateQ (Security.adversaryImpl secretKey)
          (QueryCounting.counted Direct.IsDirectHashQuery computation)).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [QueryCounting.counted_pure]
  | query_bind input next ih =>
      rw [QueryCounting.counted_query_bind]
      rcases input with world | request
      · simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
          QueryImpl.withAddCost_apply, QueryImpl.ofLift_apply, WriterT.run_bind,
          WriterT.run_monadLift, WriterT.run_map', Modes.run_liftM_of_liftM',
          AddWriterT.run_addTell, pure_bind, bind_map_left, map_bind, Functor.map_map, ih,
          mul_one, Security.adversaryImpl, simulateQ_map]
        congr 1
        funext answer
        rw [map_eq_bind_pure_comp]
        congr 1
        funext result
        rcases world with uniformInput | hashInput
        · simp [RandomOracleModel.hashCost, Direct.IsDirectHashQuery, Direct.isDirectHashQuery]
        · simp only [RandomOracleModel.hashCost, Direct.IsDirectHashQuery, Direct.isDirectHashQuery]
          simp
          rw [mul_assoc]
      · change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
        change ∀ u : Option Signature, _ at ih
        simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
          WriterT.run_bind]
        rw [Attack.signingOracleCounted_run xmss secretKey requestCost request,
          countHashQueries_xmss_sign]
        have hlift : ((liftM (xmss.sign secretKey request.epoch request.message) :
            WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (Option Signature))).run =
            (fun answer => (answer, ∅)) <$> xmss.sign secretKey request.epoch request.message :=
          rfl
        have hlog : (do
            let answer ← (liftM (xmss.sign secretKey request.epoch request.message) :
              WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (Option Signature))
            tell [⟨request, answer⟩]
            pure answer : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run =
            (fun answer => (answer, [⟨request, answer⟩])) <$>
              xmss.sign secretKey request.epoch request.message := by
          simp [WriterT.run_bind, hlift, WriterT.run_tell, WriterT.run_pure]
        simp only [Security.adversaryImpl, SUFCMA.signingOracle, QueryImpl.withLogging_apply,
          QueryCounting.counted_query_bind]
        rw [hlog]
        have ih' : ∀ answer : Option Signature,
            (WriterT.run (simulateQ
              ((QueryImpl.ofLift OracleWorld
                (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))).withAddCost
                  (RandomOracleModel.hashCost HashInput HashOutput) +
                SUFCMA.signingOracleCounted (RandomOracleModel.hashCost HashInput HashOutput)
                  requestCost xmss secretKey) (next answer))).run =
            (fun result : (α × ℕ) × QueryLog SigningSpec =>
              ((result.1.1, Multiplicative.ofAdd (result.1.2 + (requestCost + 2) * result.2.length)),
                result.2)) <$>
              (simulateQ (QueryImpl.ofLift OracleWorld
                  (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
                QueryImpl.withLogging fun request : SignRequest =>
                  xmss.sign secretKey request.epoch request.message)
                (QueryCounting.counted Direct.IsDirectHashQuery (next answer))).run := ih
        simp only [WriterT.run_map, WriterT.run_map', ih', map_bind, bind_map_left,
          Functor.map_map, simulateQ_pure, WriterT.run_pure, simulateQ_bind, WriterT.run_bind,
          bind_pure_comp, Direct.not_isDirectHashQuery_sign, if_false, zero_add, map_pure]
        congr 1
        funext answer
        congr 1
        funext result
        have hempty : (∅ : QueryLog SigningSpec) = [] := rfl
        simp only [hempty, List.append_nil, List.singleton_append, List.length_cons,
          ← ofAdd_add]
        congr 3
        ring

/-- Every execution of the adversary after any reachable key generation pays, in the statement's
signer mode, its direct hash queries and `requestCost + 2` per request. -/
theorem adversary_weighted_bound (adversary : Security.StatementAdversary) (requests : Bool)
    (q : ℕ) (hbound : (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound xmss adversary q)
    (publicKey : PublicKey) (secretKey : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (hkeys : ((publicKey, secretKey), cache) ∈ support ((simulateQ romImpl xmss.keygen).run ∅))
    (result : ((Forgery × ℕ) × QueryLog SigningSpec) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (simulateQ (Security.adversaryImpl secretKey)
      (QueryCounting.counted Direct.IsDirectHashQuery (adversary.main publicKey))).run).run cache)) :
    result.1.1.2 + ((if requests then 1 else 0) + 2) * result.1.2.length ≤ q := by
  rcases result with ⟨⟨⟨forgery, direct⟩, log⟩, finalCache⟩
  obtain ⟨verification, hverification⟩ := probComp_support_nonempty
    ((simulateQ romImpl (xmss.verify publicKey forgery.epoch forgery.message
      forgery.signature)).run finalCache)
  have h := hbound (decide (SigningTranscript.Valid log ∧
      ¬SigningTranscript.Contains log forgery) && verification.1,
    direct + ((if requests then 1 else 0) + 2) * log.length)
  refine h ?_
  simp only [SUFCMA.notion, RandomOracleModel.run]
  rw [← Security.romImpl_eq]
  unfold SUFCMA.gameCounted
  simp only [SUFCMA.costIf, Bool.false_eq_true, if_false, if_true, Modes.charge_zero,
    bind_map_left, statementCountedRun_eq]
  rw [StateT.run'_eq, support_map]
  refine ⟨((decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) &&
    verification.1, direct + ((if requests then 1 else 0) + 2) * log.length),
    verification.2), ?_, rfl⟩
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨((publicKey, secretKey), cache), hkeys, (((forgery, direct), log), finalCache), hresult,
    verification, hverification, ?_⟩
  simp


theorem logsRequests_adversaryImpl (secretKey : Seeded.SecretKey) :
    LogsRequests (Security.adversaryImpl secretKey) := by
  constructor
  · intro input cache step hstep
    have hlift : ((liftM (OracleWorld.query input) :
        WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (OracleWorld.Range input))).run =
        (fun answer => (answer, ∅)) <$> liftM (OracleWorld.query input) := rfl
    simp only [Security.adversaryImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply] at hstep
    rw [hlift, simulateQ_map, StateT.run_map, support_map] at hstep
    obtain ⟨_, _, rfl⟩ := hstep
    rfl
  · intro request cache step hstep
    simp only [Security.adversaryImpl, QueryImpl.add_apply_inr, SUFCMA.signingOracle,
      QueryImpl.withLogging_apply, WriterT.run_bind, WriterT.run_tell, WriterT.run_pure,
      simulateQ_bind, simulateQ_map, simulateQ_pure] at hstep
    have hlift : ((liftM (xmss.sign secretKey request.epoch request.message) :
        WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) (Option Signature))).run =
        (fun answer => (answer, ∅)) <$> xmss.sign secretKey request.epoch request.message :=
      rfl
    simp only [hlift, bind_map_left, pure_bind, map_bind, simulateQ_bind, simulateQ_map,
      simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure, support_bind,
      support_map, support_pure, Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff,
      exists_prop] at hstep
    obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, rfl⟩ := hstep
    simp

/-- Pruning at the weighted budget does not change the success probability. -/
theorem forgeAdvantage_pruneWeighted_eq (adversary : Security.StatementAdversary)
    (requests : Bool) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound xmss adversary q) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) =
      forgeAdvantage Seeded.scheme
        ⟨fun publicKey => pruneWeighted ((if requests then 1 else 0) + 2) q
          (adversary.main publicKey)⟩ := by
  unfold forgeAdvantage
  refine congrArg (fun computation => Pr[= true | computation]) ?_
  unfold gameCore
  simp only [simulateQ_bind, StateT.run'_bind']
  refine bind_congr_of_forall_mem_support _ fun keys hkeys => ?_
  rcases keys with ⟨⟨publicKey, secretKey⟩, cache⟩
  dsimp only
  unfold Seeded.gameRest
  simp only [simulateQ_bind, StateT.run'_bind']
  have hprune := simulateQ_pruneWeighted_eq_logged (Security.adversaryImpl secretKey)
    (logsRequests_adversaryImpl secretKey) ((if requests then 1 else 0) + 2)
    (adversary.main publicKey) q cache
    (fun result hresult => adversary_weighted_bound adversary requests q hbound publicKey
      secretKey cache hkeys result hresult)
  exact congrArg (fun computation => computation >>= _) hprune.symm

theorem memoize_noSign {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache SigningSpec) (h : computation.IsQueryBoundP IsSignQuery 0) :
    (DeterministicSigning.memoize computation cache).IsQueryBoundP IsSignQuery 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [DeterministicSigning.memoize_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [DeterministicSigning.memoize_base, isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer cache (by simpa [IsSignQuery] using h.2 answer)⟩
      | inr request => simp [IsSignQuery] at h

/-- Below the cost of one request in a signer mode, the advantage is at most
`(2q + 2) / 2^128 + q / 2^256`. -/
theorem signer_small_advantage_le (requests : Bool) (adversary : Security.StatementAdversary)
    (q : ℕ) (hq : q < (if requests then 1 else 0) + 2)
    (hbound : (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, requests⟩).advantage xmss adversary ≤
      ((2 * q + 2 : ℕ) : ℝ≥0∞) * digestInverse + q / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  rw [Modes.advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    Modes.notion_direct_advantage_eq, Security.notionDirect_advantage_eq,
    forgeAdvantage_pruneWeighted_eq adversary requests q hbound]
  let pruned : Adversary := ⟨fun publicKey =>
    pruneWeighted ((if requests then 1 else 0) + 2) q (adversary.main publicKey)⟩
  have hdirect : Direct.IsDirectQueryBound pruned q := fun publicKey =>
    pruneWeighted_isQueryBoundP_direct _ q _
  have hnoSign : NoSignQueries (Seeded.memoAdversary pruned) := fun publicKey =>
    memoize_noSign _ ∅ (pruneWeighted_isQueryBoundP_sign _ q hq _)
  refine (Seeded.forgeAdvantage_deterministic_le_reference_direct pruned q hdirect).trans ?_
  exact add_le_add (forgeAdvantage_le_of_noSignQueries _ q
    (Seeded.memoAdversary_isDirectQueryBound pruned q hdirect) hnoSign) le_rfl

/-- info: 'XmssSecurity.NoSign.signer_small_advantage_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_small_advantage_le

end XmssSecurity.NoSign

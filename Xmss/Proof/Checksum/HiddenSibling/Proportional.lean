import Xmss.Proof.Checksum.HiddenSibling.Weighted
import Xmss.Proof.Generic.Direct.StructuralQueries
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-!
# Counting the adversary's actions in the game

The expected queries of the game's adversary phase at inputs the signer never queries are the
adversary's own expected direct queries at those inputs (`expectedQueries_adversaryPhase_eq`).
The probability that the adversary signs at all is at most its expected number of requests
(`probEvent_signingLog_ne_nil_le`). On the executions without a request, the adversary phase is
its run with every oracle forwarded (`probEvent_adversaryPhase_noSign_le`); on the executions
with a request, it is the run of its hash-free pruning (`probEvent_adversaryPhase_sign_eq`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.Checksum.HiddenSibling

/-! ## The signer queries only encoding inputs -/

section Signer

variable (predicate : HashInput → Prop) [DecidablePred predicate] (secretKey : Generic.SecretKey)
  (hencoding : ∀ leafIndex payload,
    ¬ predicate (CacheView.encodingInput secretKey.parameter leafIndex payload))

include hencoding

theorem precomputedSignAttempt_zero (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Generic.Signature)).IsQueryBoundP predicate 0 := by
  rw [Generic.Signing.precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_
  · have hnot := hencoding leafIndex (message, randomness)
    simp only [CacheView.encodingInput] at hnot
    simp [Generic.Hashing.encodingHash, Generic.Hashing.tweakableHash, Generic.Hashing.oracleHash, hnot]
  · intro digest _
    split <;> simp

theorem scheme_sign_zero (leafIndex : LeafIndex) (message : Message) :
    (precomputedScheme.sign secretKey leafIndex message).IsQueryBoundP
      (RandomOracle.IsRelevantHashQuery predicate) 0 := by
  change (Signing.precomputedCappedSign secretKey leafIndex message).IsQueryBoundP _ 0
  rw [Signing.precomputedCappedSign]
  generalize Code.signingAttemptLimit = attempts
  induction attempts with
  | zero =>
      rw [Signing.precomputedSignBoundedAttempts]
      exact OracleComp.isQueryBoundP_pure _ _ _
  | succ attempts ih =>
      rw [Signing.precomputedSignBoundedAttempts]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (OracleComp.IsQueryBoundP.liftComp_subSpec (p := fun _ : unifSpec.Domain => False)
          (fun _ => Iff.rfl) (OracleComp.isQueryBoundP_false _ 0)) ?_
      intro randomness _
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_
      · change (liftComp (Generic.Signing.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp HashSpec (Option Generic.Signature)) OracleWorld).IsQueryBoundP _ _
        exact OracleComp.IsQueryBoundP.liftComp_subSpec (p := predicate) (fun _ => Iff.rfl)
          (precomputedSignAttempt_zero predicate secretKey hencoding leafIndex message randomness)
      · intro result _
        cases result with
        | none => exact ih
        | some signature => exact OracleComp.isQueryBoundP_pure _ _ _

theorem expectedQueries_sign_eq_zero (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (RandomOracle.IsRelevantHashQuery predicate)
      (precomputedScheme.sign secretKey leafIndex message) cache = 0 := by
  have h := expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ cache 0
    (scheme_sign_zero predicate secretKey hencoding leafIndex message)
  simpa using h

/-- The adversary phase's expected queries at inputs the signer never queries. -/
theorem expectedQueries_adversaryPhase_eq (adversary : Adversary) (publicKey : PublicKey)
    (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (RandomOracle.IsRelevantHashQuery predicate)
        (Deciding.adversaryPhase adversary publicKey secretKey) cache =
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectWorldQuery (RandomOracle.IsRelevantHashQuery predicate))
        (adversary.main publicKey) cache := by
  have hproj := QueryImpl.fst_map_run_withTraceAppend
    (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) signingLogFragment
    (adversary.main publicKey)
  rw [cappedSourceUnloggedMappedAdversaryImpl_withTraceAppend_eq] at hproj
  have hcount := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl
      (RandomOracle.IsRelevantHashQuery predicate) computation cache) hproj
  rw [expectedSimulatedQueryCount_map] at hcount
  unfold Deciding.adversaryPhase
  rw [hcount]
  exact Direct.expectedSimulatedQueryCount_mappedAdversary_eq publicKey secretKey _
    (fun request cache => expectedQueries_sign_eq_zero predicate secretKey hencoding
      request.epoch request.message cache) (adversary.main publicKey) cache

end Signer

theorem expectedDirectWorld_le_direct {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (predicate : HashInput → Prop) [DecidablePred predicate]
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : σ) :
    expectedSimulatedQueryCount impl
        (Direct.IsDirectWorldQuery (RandomOracle.IsRelevantHashQuery predicate)) computation state ≤
      expectedSimulatedQueryCount impl Direct.IsDirectHashQuery computation state := by
  refine expectedSimulatedQueryCount_mono impl _ _ (fun input hinput => ?_) computation state
  rcases input with (uniformInput | hashInput) | request
  · exact hinput.elim
  · simp
  · exact hinput.elim

/-! ## The probability of signing -/

theorem forwardOracles_run_eq (input : OracleWorld.Domain) :
    (forwardOracles input).run =
      (fun answer => (answer, ([] : QueryLog SigningSpec))) <$>
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _) := rfl

theorem romImpl_forwardOracles_run (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (forwardOracles input).run).run cache =
      (fun result => ((result.1, ([] : QueryLog SigningSpec)), result.2)) <$>
        (romImpl input).run cache := by
  rw [forwardOracles_run_eq, simulateQ_map, simulateQ_spec_query, StateT.run_map]

/-- The adversary signs with probability at most its expected number of requests. -/
theorem probEvent_signingLog_ne_nil_le {α : Type} (publicKey : PublicKey)
    (secretKey : Generic.SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    Pr[fun result : (α × QueryLog SigningSpec) × QueryCache HashSpec => result.1.2 ≠ [] |
      (simulateQ romImpl (simulateQ (forwardOracles + signingOracle precomputedScheme secretKey)
        computation).run).run cache] ≤
      expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        IsSignQuery computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp
  | query_bind input next ih =>
      rw [Direct.run_logged_query_bind, expectedSimulatedQueryCount_query_bind]
      rcases input with world | request
      · simp only [IsSignQuery, if_false, zero_add]
        rw [show (forwardOracles + signingOracle precomputedScheme secretKey) (.inl world) =
          forwardOracles world from rfl, romImpl_forwardOracles_run, probEvent_bind_eq_tsum,
          tsum_probOutput_map_mul]
        refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
        rw [probEvent_map]
        refine (probEvent_mono fun outcome _ houtcome => ?_).trans (ih result.1 result.2)
        simpa using houtcome
      · simp only [IsSignQuery, if_true]
        exact probEvent_le_one.trans le_self_add

/-! ## Executions without a request -/

/-- The game's adversary phase from a cache. -/
noncomputable abbrev realRun {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    ProbComp ((α × QueryLog SigningSpec) × QueryCache HashSpec) :=
  (simulateQ romImpl (simulateQ (forwardOracles + signingOracle precomputedScheme secretKey)
    computation).run).run cache

theorem withLogging_run_eq (signer : SignRequest → OracleComp OracleWorld (Option Generic.Signature))
    (request : SignRequest) :
    (QueryImpl.withLogging signer request).run =
      (fun answer => (answer, [⟨request, answer⟩])) <$> signer request := by
  simp [QueryImpl.withLogging_apply, WriterT.run_bind, WriterT.run_tell]

theorem signingOracle_run_log (secretKey : Generic.SecretKey) (request : SignRequest)
    (cache : QueryCache HashSpec)
    (step : (Option Generic.Signature × QueryLog SigningSpec) × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ romImpl
      (signingOracle precomputedScheme secretKey request).run).run cache)) :
    step.1.2 ≠ [] := by
  have hrun : (signingOracle precomputedScheme secretKey request).run =
      (fun answer => (answer, [⟨request, answer⟩])) <$>
        precomputedScheme.sign secretKey request.epoch request.message :=
    withLogging_run_eq (fun request => precomputedScheme.sign secretKey request.epoch
      request.message) request
  rw [hrun, simulateQ_map, StateT.run_map, support_map] at hstep
  obtain ⟨_, _, rfl⟩ := hstep
  simp

/-- Without a request on any branch, every execution has an empty signing log. -/
theorem realRun_log_eq_nil {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : computation.IsQueryBoundP IsSignQuery 0) (cache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hresult : result ∈ support (realRun secretKey computation cache)) :
    result.1.2 = [] := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [realRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst hresult
      rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      unfold realRun at hresult
      rw [Direct.run_logged_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hrest⟩ := hresult
      rcases input with world | request
      · rw [show (forwardOracles + signingOracle precomputedScheme secretKey) (.inl world) =
          forwardOracles world from rfl, romImpl_forwardOracles_run, support_map] at hstep
        obtain ⟨first, _, rfl⟩ := hstep
        rw [support_map] at hrest
        obtain ⟨rest, hrestMem, rfl⟩ := hrest
        simpa using ih first.1 (by simpa [IsSignQuery] using h.2 first.1) first.2 rest hrestMem
      · simp [IsSignQuery] at h

/-- On the executions without a request, the adversary phase is the forwarded run. -/
theorem probEvent_realRun_noSign_le {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (event : α × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) ∧ result.1.2 = [] |
        realRun secretKey computation cache] ≤
      Pr[event | (simulateQ romImpl (simulateQ forwardOnly computation)).run cache] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      classical
      simp only [realRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure, probEvent_pure]
      split_ifs <;> simp_all
  | query_bind input next ih =>
      unfold realRun
      rw [Direct.run_logged_query_bind]
      rcases input with world | request
      · have hforward : (simulateQ romImpl (simulateQ forwardOnly
            (liftM ((OracleWorld + SigningSpec).query (.inl world)) >>= next))).run cache =
            (romImpl world).run cache >>= fun result =>
              (simulateQ romImpl (simulateQ forwardOnly (next result.1))).run result.2 := by
          rw [simulateQ_query_bind]
          change (simulateQ romImpl (liftM (OracleWorld.query world) >>= fun answer =>
            simulateQ forwardOnly (next answer))).run cache = _
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        rw [show (forwardOracles + signingOracle precomputedScheme secretKey) (.inl world) =
            forwardOracles world from rfl, romImpl_forwardOracles_run, probEvent_bind_eq_tsum,
          tsum_probOutput_map_mul, hforward, probEvent_bind_eq_tsum]
        refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
        rw [probEvent_map]
        refine (probEvent_mono fun outcome _ houtcome => ?_).trans (ih result.1 result.2)
        simpa using houtcome
      · rw [probEvent_eq_zero fun outcome houtcome hevent => ?_]
        · exact zero_le
        rw [mem_support_bind_iff] at houtcome
        obtain ⟨step, hstep, hrest⟩ := houtcome
        rw [support_map] at hrest
        obtain ⟨rest, _, rfl⟩ := hrest
        exact signingOracle_run_log secretKey request cache step hstep
          (List.append_eq_nil_iff.mp hevent.2).1

/-! ## Executions with a request -/

/-- A program without direct hash queries is unchanged by answering them without querying. -/
theorem pruneDirect_zero_eq_self {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : computation.IsQueryBoundP Direct.IsDirectHashQuery 0) :
    Direct.pruneDirect 0 computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rcases input with (uniformInput | hashInput) | request
      · rw [Direct.pruneDirect_uniform_bind]
        exact congrArg _ (funext fun answer => ih answer (by simpa using h.2 answer))
      · simp at h
      · rw [Direct.pruneDirect_sign_bind]
        exact congrArg _ (funext fun answer => ih answer (by simpa using h.2 answer))

/-- When a request can only come first, the executions with a request are those of the
hash-free pruning. -/
theorem probEvent_realRun_sign_eq {α : Type} (secretKey : Generic.SecretKey) (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) (hbudget : budget ≤ signCost)
    (cache : QueryCache HashSpec)
    (event : (α × QueryLog SigningSpec) × QueryCache HashSpec → Prop) :
    Pr[fun result => event result ∧ result.1.2 ≠ [] | realRun secretKey computation cache] =
      Pr[fun result => event result ∧ result.1.2 ≠ [] |
        realRun secretKey (Direct.pruneDirect 0 computation) cache] := by
  induction computation using OracleComp.inductionOn generalizing budget cache event with
  | pure value => rfl
  | query_bind input next ih =>
      have hfull := h
      rw [isWeightedBound_query_bind_iff] at h
      rcases input with (uniformInput | hashInput) | request
      · rw [Direct.pruneDirect_uniform_bind]
        unfold realRun
        rw [Direct.run_logged_query_bind, Direct.run_logged_query_bind, probEvent_bind_eq_tsum,
          probEvent_bind_eq_tsum,
          show (forwardOracles + signingOracle precomputedScheme secretKey)
            (.inl (.inl uniformInput)) = forwardOracles (.inl uniformInput) from rfl]
        refine tsum_congr fun step => ?_
        by_cases hstep : step ∈ support ((simulateQ romImpl
            (forwardOracles (.inl uniformInput)).run).run cache)
        · have hlog : step.1.2 = [] := by
            rw [romImpl_forwardOracles_run, support_map] at hstep
            obtain ⟨_, _, rfl⟩ := hstep
            rfl
          congr 1
          rw [probEvent_map, probEvent_map]
          simp only [Function.comp_def, hlog, List.nil_append]
          exact ih step.1.1 _ (h.2 step.1.1) (by simpa [actionWeight] using hbudget) step.2 _
        · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul, zero_mul]
      · -- After a hash query no request follows: neither side signs.
        have hlow : budget - actionWeight signCost (.inl (.inr hashInput)) < signCost := by
          have := h.1
          simp [actionWeight] at this ⊢
          omega
        have hnone : (liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>=
            next).IsQueryBoundP IsSignQuery 0 := by
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
            simpa [IsSignQuery] using (h.2 answer).noSign hlow⟩
        rw [Direct.pruneDirect_hash_bind, if_pos rfl,
          probEvent_eq_zero fun result hresult hevent =>
            hevent.2 (realRun_log_eq_nil secretKey _ hnone cache result hresult),
          probEvent_eq_zero fun result hresult hevent =>
            hevent.2 (realRun_log_eq_nil secretKey _
              ((pruneDirect_zero_isWeightedBound signCost _ _ (h.2 default)).noSign hlow)
              cache result hresult)]
      · -- The request comes first; afterwards the program has no direct hash query.
        rw [Direct.pruneDirect_sign_bind]
        have hzero : budget - actionWeight signCost (.inr request) = 0 := by
          have := h.1
          simp [actionWeight] at this ⊢
          omega
        have hrest : ∀ answer, Direct.pruneDirect 0 (next answer) = next answer := by
          intro answer
          have hdirect := (h.2 answer).direct
          rw [hzero] at hdirect
          exact pruneDirect_zero_eq_self _ hdirect
        simp only [hrest]

end Xmss.Checksum.HiddenSibling

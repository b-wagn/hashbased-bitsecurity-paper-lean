import XmssSecurity.Proof.TargetSum.PrecomputedBoundedSign
import XmssSecurity.Proof.TargetSum.OutcomeClassification
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Seeded.CacheCoupling
import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Proof.Common.RepeatedEpochs
import XmssSecurity.Proof.TargetSum.Direct.Bridge

/-!
# Signing failures are the only correctness failures of the target-sum scheme

Every signature the target-sum signer returns verifies, whatever the adversary queries; the
argument is that of `Proof/Checksum/Correctness.lean`. The signer may instead return `⊥`, after
`A_max` randomizer trials whose digests all fail to decode. Then every trial left its randomizer
and its digest in the oracle's cache (`SigningFails`), so a run of the correctness experiment that
sets the flag `v` ends in a cache where some request's trials all failed
(`experiment_flag_signingFails`). `SigningFailure.lean` bounds the probability of such a cache.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Correct

open Seeded

noncomputable local instance : IsUniformSpec HashSpec := IsUniformSpec.ofFintypeInhabited _

-- Unfolding the master-seed sampler enumerates `2^256` seeds; keep it opaque.
attribute [local irreducible] sampleMasterSeed

/-! ### Caches that agree outside a set of inputs -/

/-- A run that makes no `bad` query, from a cache, can be replayed from any cache that agrees with
it outside `bad` and has no `bad` entry. -/
theorem run_support_agreeOutside {β : Type} (computation : OracleComp HashSpec β)
    (bad : HashInput → Prop) [DecidablePred bad] (hbound : computation.IsQueryBoundP bad 0)
    (cache other : QueryCache HashSpec) (hagree : AgreeOutside bad cache other)
    (hle : other ≤ cache) (hclean : ∀ input, bad input → other input = none) :
    ∀ result ∈ support ((simulateQ randomOracle computation).run cache),
      ∃ otherCache, (result.1, otherCache) ∈ support ((simulateQ randomOracle computation).run other) ∧
        otherCache ≤ result.2 ∧ (∀ input, bad input → otherCache input = none) := by
  induction computation using OracleComp.inductionOn generalizing cache other with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      exact ⟨other, by simp, hle, hclean⟩
  | query_bind input next ih =>
      intro result hresult
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hgood : ¬bad input := by simpa using hbound.1
      have hnext : ∀ answer, (next answer).IsQueryBoundP bad 0 := fun answer => by
        simpa [hgood] using hbound.2 answer
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨answer, middle⟩, hquery, hrest⟩ := hresult
      have hquery' : (answer, middle) ∈ support ((randomOracle (spec := HashSpec) input).run cache) := by
        simpa only [simulateQ_spec_query] using hquery
      cases hcached : cache input with
      | some output =>
          rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
            Set.mem_singleton_iff] at hquery'
          obtain ⟨hanswer, hmiddle⟩ := Prod.mk.inj hquery'
          rw [hmiddle] at hrest
          rw [← hanswer] at hcached
          have hother : other input = some answer := by rw [← hagree input hgood]; exact hcached
          obtain ⟨otherCache, hotherRun, hotherLe, hotherClean⟩ :=
            ih answer (hnext answer) cache other hagree hle hclean result hrest
          refine ⟨otherCache, ?_, hotherLe, hotherClean⟩
          rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
          refine ⟨(answer, other), ?_, hotherRun⟩
          simp only [simulateQ_spec_query]
          rw [QueryImpl.withCaching_run_some _ hother]
          simp
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery'
          obtain ⟨sampled, hsampled, hpair⟩ := hquery'
          obtain ⟨hanswer, hmiddle⟩ := Prod.mk.inj hpair
          subst hanswer
          rw [← hmiddle] at hrest
          have hother : other input = none := by rw [← hagree input hgood]; exact hcached
          obtain ⟨otherCache, hotherRun, hotherLe, hotherClean⟩ :=
            ih sampled (hnext sampled) (cache.cacheQuery input sampled)
              (other.cacheQuery input sampled) (hagree.cacheQuery input sampled)
              (fun i o hi => by
                by_cases heq : i = input
                · subst heq; simpa using hi
                · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hi ⊢; exact hle hi)
              (fun i hi => by
                by_cases heq : i = input
                · subst heq; exact absurd hi hgood
                · rw [QueryCache.cacheQuery_of_ne _ _ heq]; exact hclean i hi)
              result hrest
          refine ⟨otherCache, ?_, hotherLe, hotherClean⟩
          rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
          refine ⟨(sampled, other.cacheQuery input sampled), ?_, hotherRun⟩
          simp only [simulateQ_spec_query]
          rw [QueryImpl.withCaching_run_none _ hother, support_map]
          exact ⟨sampled, hsampled, rfl⟩

/-- A run whose queries are all `bad`, from a cache whose entries are all `bad`, ends in a cache
whose entries are all `bad`. -/
theorem run_support_onlyBad {β : Type} (computation : OracleComp HashSpec β)
    (bad : HashInput → Prop) [DecidablePred bad]
    (hbound : computation.IsQueryBoundP (fun input => ¬bad input) 0)
    (cache : QueryCache HashSpec) (honly : ∀ input, ¬bad input → cache input = none) :
    ∀ result ∈ support ((simulateQ randomOracle computation).run cache),
      ∀ input, ¬bad input → result.2 input = none := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      exact honly
  | query_bind input next ih =>
      intro result hresult
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hbad : bad input := by simpa using hbound.1
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨⟨answer, middle⟩, hquery, hrest⟩ := hresult
      refine ih answer (by simpa [hbad] using hbound.2 answer) middle ?_ result hrest
      intro other hother
      have hquery' : (answer, middle) ∈ support ((randomOracle (spec := HashSpec) input).run cache) := by
        simpa only [simulateQ_spec_query] using hquery
      have hne : other ≠ input := fun h => hother (h ▸ hbad)
      cases hcached : cache input with
      | some output =>
          rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
            Set.mem_singleton_iff] at hquery'
          rw [(Prod.mk.inj hquery').2]
          exact honly other hother
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery'
          obtain ⟨sampled, -, hpair⟩ := hquery'
          rw [← (Prod.mk.inj hpair).2, QueryCache.cacheQuery_of_ne _ _ hne]
          exact honly other hother

/-! ### Key generation -/

theorem sequenceFin_isQueryBoundP {α : Type} {p : HashInput → Prop} [DecidablePred p] :
    ∀ {n : Nat} (computation : Fin n → OracleComp HashSpec α),
      (∀ index, (computation index).IsQueryBoundP p 0) →
        (Concrete.sequenceFin computation).IsQueryBoundP p 0
  | 0, _, _ => by simp [Concrete.sequenceFin]
  | n + 1, computation, h => by
      simp only [Concrete.sequenceFin]
      have hhead := h 0
      have htail := sequenceFin_isQueryBoundP (fun index : Fin n => computation index.succ)
        (fun index => h index.succ)
      have hbind : IsQueryBoundP (computation 0 >>= fun head =>
          Concrete.sequenceFin (fun index : Fin n => computation index.succ) >>= fun tail =>
            (pure (Fin.cases head tail) : OracleComp HashSpec (Fin (n + 1) → α))) p (0 + (0 + 0)) :=
        isQueryBoundP_bind hhead fun head _ => isQueryBoundP_bind htail fun tail _ =>
          isQueryBoundP_pure p _ 0
      simpa using hbind

theorem deriveKey_onlySeed (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    (deriveKey parameter domain seed : OracleComp HashSpec Digest).IsQueryBoundP
      (fun input => ¬MaySeedHit input) 0 := by
  simp [deriveKey, Concrete.oracleHash, maySeedHit_keygenHashInput]

theorem romImpl_liftM_support {α : Type} (computation : ProbComp α)
    (cache : QueryCache HashSpec) :
    support ((simulateQ romImpl (liftM computation : OracleComp OracleWorld α)).run cache) =
      (fun x => (x, cache)) '' support computation :=
  roSim.run_liftM_support (hashSpec := HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) computation cache

/-- Every seeded key is a key of the precomputed key generation, whose cache is contained in the
seeded key generation's cache. -/
theorem seededKeygen_support_precomputed (seed : MasterSeed)
    (keyResult : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅)) :
    ∃ cache, ((keyResult.1.1, keyResult.1.2.precomputed), cache) ∈
        support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) ∧
      cache ≤ keyResult.2 ∧
      ∀ largerCache, cache ≤ largerCache → keyResult.1.1 =
        Concrete.CacheReplay.publicKeyFromCache largerCache keyResult.1.2.precomputed := by
  unfold Seeded.keygenFromSeed at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨secret, secretCache⟩, hsecret, hmem⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨tree, treeCache⟩, htree, hmem⟩ := hmem
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
  subst hmem
  have hparameterOnly := run_support_onlyBad _ MaySeedHit
    (deriveKey_onlySeed 0 .parameter seed) ∅ (fun _ _ => rfl) _ hparameter
  have hsecretOnly := run_support_onlyBad _ MaySeedHit
    (sequenceFin_isQueryBoundP _ fun leafIndex => sequenceFin_isQueryBoundP _ fun chain =>
      deriveKey_onlySeed parameter (.chain leafIndex chain) seed) parameterCache hparameterOnly _
    hsecret
  have hnoSeed : ((Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).withQueryLog).IsQueryBoundP MaySeedHit 0 :=
    (isQueryBoundP_run_simulateQ_loggingOracle_iff _ _ _).2
      (Concrete.treeNode_noSeed _ _ _ _)
  obtain ⟨cache, hcacheRun, hcacheLe, -⟩ := run_support_agreeOutside _ MaySeedHit hnoSeed
    secretCache ∅ (fun input hinput => hsecretOnly input hinput) (fun _ _ h => by simp at h)
    (fun _ _ => rfl) _ htree
  have hlog : hashCacheOfLog tree.2 = cache :=
    hashCacheOfLog_eq_finalCache_of_empty _ (tree, cache) hcacheRun
  have htreeRun : (tree.1, cache) ∈ support ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅) := by
    rw [← withQueryLog_cache_projection, support_map]
    exact ⟨(tree, cache), hcacheRun, rfl⟩
  refine ⟨cache, ?_, hcacheLe, fun largerCache hle => ?_⟩
  swap
  · have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest) ∅ cache largerCache tree.1 htreeRun hle
    rw [Concrete.CacheReplay.eval_treeNode] at heval
    exact Concrete.CacheReplay.publicKey_eq_publicKeyFromCache largerCache
      (Concrete.precomputedSecretKey parameter secret (hashCacheOfLog tree.2)) tree.1 heval.symm
  unfold Concrete.precomputedKeygen Concrete.samplePublicParameter Concrete.sampleSecret
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(parameter, ∅), ?_, ?_⟩
  · rw [romImpl_liftM_support]
    refine ⟨parameter, ?_, rfl⟩
    rw [support_uniformSample]
    trivial
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(secret, ∅), ?_, ?_⟩
  · rw [romImpl_liftM_support]
    refine ⟨secret, ?_, rfl⟩
    rw [support_uniformSample]
    trivial
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(tree, cache), ?_, ?_⟩
  · rw [show simulateQ romImpl (liftM ((Concrete.treeNode parameter secret treeHeight
        Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog) :
        OracleComp OracleWorld _) = simulateQ randomOracle ((Concrete.treeNode parameter secret
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog) from
      QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _]
    exact hcacheRun
  · simp [hlog]

/-! ### Failed trials -/

/-- Trial `trial` of signing `message` at `leafIndex` failed in `cache`: the trial's randomizer and
the digest of the message under it are cached, and the digest does not decode. -/
def TrialFails (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (cache : QueryCache HashSpec) (trial : ℕ) : Prop :=
  ∃ randomizerOutput, cache (randomizerHashInput parameter seed leafIndex message
      (BitVec.ofNat 32 trial)) = some randomizerOutput ∧
    ∃ digestOutput, cache (Concrete.CacheView.encodingInput parameter leafIndex
        (message, randomizerOutput.extractLsb' 0 randomnessBits)) = some digestOutput ∧
      TargetSum.decodeDigest (truncateHash digestOutput) = none

/-- All `A_max` trials of signing `message` at `leafIndex` failed in `cache`. -/
def SigningFails (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (cache : QueryCache HashSpec) : Prop :=
  ∀ trial < signingAttemptLimit, TrialFails parameter seed leafIndex message cache trial

theorem TrialFails.mono {parameter : PublicParameter} {seed : MasterSeed}
    {leafIndex : LeafIndex} {message : Message} {cache largerCache : QueryCache HashSpec}
    {trial : ℕ} (hle : cache ≤ largerCache)
    (h : TrialFails parameter seed leafIndex message cache trial) :
    TrialFails parameter seed leafIndex message largerCache trial := by
  obtain ⟨randomizerOutput, hrandomizer, digestOutput, hdigest, hdecode⟩ := h
  exact ⟨randomizerOutput, hle hrandomizer, digestOutput, hle hdigest, hdecode⟩

theorem SigningFails.mono {parameter : PublicParameter} {seed : MasterSeed}
    {leafIndex : LeafIndex} {message : Message} {cache largerCache : QueryCache HashSpec}
    (hle : cache ≤ largerCache) (h : SigningFails parameter seed leafIndex message cache) :
    SigningFails parameter seed leafIndex message largerCache :=
  fun trial htrial => (h trial htrial).mono hle

/-! ### Signing and verification -/

/-- A signing attempt either returns `⊥`, leaving an undecodable digest in the cache, or a
signature that, from any cache above the key's cache, is the cache-level signature of the decoded
encoding. -/
theorem precomputedSignAttempt_outcome (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (keyCache initialCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey)
    (step : Option Signature × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ randomOracle
      (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))).run initialCache)) :
    initialCache ≤ step.2 ∧
    (step.1 = none → ∃ digestOutput, step.2 (Concrete.CacheView.encodingInput
        secretKey.parameter leafIndex (message, randomness)) = some digestOutput ∧
      TargetSum.decodeDigest (truncateHash digestOutput) = none) ∧
    (∀ signature, step.1 = some signature →
      ∀ largerCache, keyCache ≤ largerCache → step.2 ≤ largerCache →
        ∃ encoding,
          TargetSum.decodeDigest (Concrete.CacheView.encodingHash largerCache secretKey.parameter
            leafIndex (message, randomness)) = some encoding ∧
          signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey leafIndex
            randomness encoding) := by
  have hle : initialCache ≤ step.2 :=
    Concrete.CacheReplay.randomOracle_cache_le _ initialCache step hstep
  unfold Concrete.precomputedSignAttempt at hstep
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨⟨digest, digestCache⟩, hdigest, hrest⟩ := hstep
  have hquery : ∃ output, digestCache (Concrete.CacheView.encodingInput secretKey.parameter
      leafIndex (message, randomness)) = some output ∧ digest = truncateHash output := by
    unfold Concrete.encodingHash Concrete.tweakableHash Concrete.oracleHash at hdigest
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hdigest
    obtain ⟨⟨output, middleCache⟩, hq, hpure⟩ := hdigest
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at hpure
    obtain ⟨rfl, rfl⟩ := hpure
    have hc := Concrete.CacheReplay.randomOracle_query_caches
      (tweakableHashInput secretKey.parameter (.encoding leafIndex)
        (Concrete.encodingPayload message randomness)) initialCache output digestCache
      (by simpa using hq)
    exact ⟨output, hc, rfl⟩
  obtain ⟨output, hcached, rfl⟩ := hquery
  have hrestLe : digestCache ≤ step.2 :=
    Concrete.CacheReplay.randomOracle_cache_le _ digestCache step hrest
  refine ⟨hle, ?_, ?_⟩
  · intro hnone
    cases hdecode : TargetSum.decodeDigest (truncateHash output) with
    | none => exact ⟨output, hrestLe hcached, hdecode⟩
    | some encoding =>
        simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hrest
        rw [hrest] at hnone
        simp at hnone
  · intro signature hsignature largerCache hkeyLe hlarger
    cases hdecode : TargetSum.decodeDigest (truncateHash output) with
    | none =>
        simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hrest
        rw [hrest] at hsignature
        simp at hsignature
    | some encoding =>
        simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hrest
        rw [hrest] at hsignature
        simp only [Option.some.injEq] at hsignature
        refine ⟨encoding, ?_, ?_⟩
        · rw [Concrete.CacheView.encodingHash,
            Concrete.CacheView.digestAt_eq_of_cache_eq_some (hlarger (hrestLe hcached))]
          exact hdecode
        · rw [← hsignature]
          exact hconsistent largerCache hkeyLe leafIndex randomness encoding

/-- The outcome of the seeded signer's trials from `trial` on: the cache grows; `⊥` means every
trial failed; and a returned signature verifies from the cache after signing. -/
theorem signFrom_outcome (secretKey : Seeded.SecretKey) (publicKey : PublicKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    (leafIndex : LeafIndex) (message : Message) :
    ∀ (attempts trial : ℕ) (cache : QueryCache HashSpec), keyCache ≤ cache →
      ∀ step ∈ support ((simulateQ randomOracle
          (Seeded.signFrom secretKey leafIndex message attempts trial :
            OracleComp HashSpec (Option Signature))).run cache),
        cache ≤ step.2 ∧
        (step.1 = none → ∀ index < attempts, TrialFails secretKey.precomputed.parameter
          secretKey.seed leafIndex message step.2 (trial + index)) ∧
        (∀ signature, step.1 = some signature →
          ∀ check ∈ support ((simulateQ randomOracle
              (Concrete.verify publicKey leafIndex message signature :
                OracleComp HashSpec Bool)).run step.2),
            check.1 = true ∧ step.2 ≤ check.2) := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial cache _ step hstep
      simp only [Seeded.signFrom, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hstep
      subst hstep
      refine ⟨le_rfl, fun _ index hindex => absurd hindex (Nat.not_lt_zero _), ?_⟩
      intro signature hsignature
      simp at hsignature
  | succ attempts ih =>
      intro trial cache hle step hstep
      have hcacheLe : cache ≤ step.2 :=
        Concrete.CacheReplay.randomOracle_cache_le _ cache step hstep
      refine ⟨hcacheLe, ?_⟩
      simp only [Seeded.signFrom] at hstep
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
      obtain ⟨⟨randomness, randomnessCache⟩, hrandomness, hstep⟩ := hstep
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hrest⟩ := hstep
      have hrandomnessLe : cache ≤ randomnessCache :=
        Concrete.CacheReplay.randomOracle_cache_le _ cache _ hrandomness
      obtain ⟨hattemptLe, hattemptNone, hattemptSome⟩ := precomputedSignAttempt_outcome
        secretKey.precomputed leafIndex message randomness keyCache randomnessCache hconsistent
        (attempt, attemptCache) hattempt
      -- the randomizer of this trial is cached
      have hrandomizer : ∃ randomizerOutput,
          randomnessCache (randomizerHashInput secretKey.precomputed.parameter secretKey.seed
            leafIndex message (BitVec.ofNat 32 trial)) = some randomizerOutput ∧
          randomizerOutput.extractLsb' 0 randomnessBits = randomness := by
        unfold deriveRandomizer Concrete.oracleHash at hrandomness
        rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrandomness
        obtain ⟨⟨output, outputCache⟩, hquery, hpure⟩ := hrandomness
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hpure
        obtain ⟨rfl, rfl⟩ := hpure
        have hc := Concrete.CacheReplay.randomOracle_query_caches
          (randomizerHashInput secretKey.precomputed.parameter secretKey.seed leafIndex message
            (BitVec.ofNat 32 trial)) cache output randomnessCache (by simpa using hquery)
        exact ⟨output, hc, rfl⟩
      cases attempt with
      | some signature =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hrest
          subst hrest
          refine ⟨fun hnone => by simp at hnone, ?_⟩
          intro signature' hsignature check hcheck
          simp only [Option.some.injEq] at hsignature
          subst hsignature
          have hfinalLe : attemptCache ≤ check.2 :=
            Concrete.CacheReplay.randomOracle_cache_le _ attemptCache check hcheck
          refine ⟨?_, hfinalLe⟩
          have hverify := Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey
            leafIndex message signature attemptCache check.2 check.1 hcheck
          have hkeyLe : keyCache ≤ check.2 :=
            hle.trans (hrandomnessLe.trans (hattemptLe.trans hfinalLe))
          obtain ⟨encoding, hdecode, hsignature⟩ :=
            hattemptSome signature rfl check.2 hkeyLe hfinalLe
          have hrandomnessEq : signature.randomness = randomness := by
            rw [hsignature]; rfl
          rw [← hverify, hkey check.2 hkeyLe, hsignature]
          exact Concrete.CacheReplay.verifyFromCache_signWithEncoding check.2
            secretKey.precomputed leafIndex message randomness encoding hdecode
      | none =>
          obtain ⟨hrestLe, hrestNone, hrestSome⟩ := ih (trial + 1) attemptCache
            (hle.trans (hrandomnessLe.trans hattemptLe)) step hrest
          refine ⟨fun hnone index hindex => ?_, hrestSome⟩
          cases index with
          | zero =>
              obtain ⟨randomizerOutput, hrandomizerCached, hrandomizerEq⟩ := hrandomizer
              obtain ⟨digestOutput, hdigestCached, hdigestDecode⟩ := hattemptNone rfl
              refine ⟨randomizerOutput, hattemptLe.trans hrestLe hrandomizerCached, digestOutput,
                ?_, hdigestDecode⟩
              rw [hrandomizerEq]
              exact hrestLe hdigestCached
          | succ index =>
              have := hrestNone hnone index (by omega)
              rwa [show trial + 1 + index = trial + (index + 1) by omega] at this

/-! ### The correctness experiment -/

/-- The adversary's run in the correctness experiment. -/
abbrev CorrectRun := Correctness.Run OracleWorld Message Signature lifetime

/-- The oracles of the correctness experiment of `xmss`. -/
noncomputable abbrev correctImpl (publicKey : PublicKey) (secretKey : Seeded.SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) CorrectRun :=
  QueryImpl.ofLift OracleWorld CorrectRun + Correctness.signingOracle xmss publicKey secretKey

theorem correctRun_query_bind {α : Type} (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : QueryLog SigningSpec × Bool) :
    (simulateQ (correctImpl publicKey secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next)).run.run state =
      (correctImpl publicKey secretKey input).run.run state >>= fun p =>
        (fun q => ((q.1.1, p.1.2 * q.1.2), q.2)) <$>
          (simulateQ (correctImpl publicKey secretKey) (next p.1.1)).run.run p.2 := by
  simp [simulateQ_bind, WriterT.run_bind, StateT.run_bind]

theorem romImpl_liftHash {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ randomOracle computation :=
  QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) computation

/-- A run can only set the flag `v` when some request's trials all failed. -/
def FlagExplained (secretKey : Seeded.SecretKey) (flag : Bool) (cache : QueryCache HashSpec) :
    Prop :=
  flag = true → ∃ leafIndex message,
    SigningFails secretKey.precomputed.parameter secretKey.seed leafIndex message cache

theorem FlagExplained.mono {secretKey : Seeded.SecretKey} {flag : Bool}
    {cache largerCache : QueryCache HashSpec} (hle : cache ≤ largerCache)
    (h : FlagExplained secretKey flag cache) : FlagExplained secretKey flag largerCache := by
  intro hflag
  obtain ⟨leafIndex, message, hfails⟩ := h hflag
  exact ⟨leafIndex, message, hfails.mono hle⟩

/-- One signing query of the correctness experiment sets the flag only by failing to sign. -/
theorem signingStep_flagExplained (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    (request : SignRequest) (signed : QueryLog SigningSpec) (flag : Bool)
    (cache : QueryCache HashSpec) (hle : keyCache ≤ cache)
    (hflag : FlagExplained secretKey flag cache) :
    ∀ step ∈ support ((simulateQ romImpl
        ((correctImpl publicKey secretKey (.inr request)).run.run (signed, flag))).run cache),
      FlagExplained secretKey step.1.2.2 step.2 ∧ cache ≤ step.2 := by
  intro step hstep
  change step ∈ support ((simulateQ romImpl
    ((Correctness.signingOracle xmss publicKey secretKey request).run.run (signed, flag))).run
      cache) at hstep
  unfold Correctness.signingOracle at hstep
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, AddWriterT.run_addTell,
    SUFCMA.writerState_run_get, pure_bind] at hstep
  split at hstep
  · simp only [WriterT.run_pure, StateT.run_pure, map_pure, simulateQ_pure, support_pure] at hstep
    subst hstep
    exact ⟨hflag, le_rfl⟩
  · simp only [WriterT.run_bind, StateT.run_bind, SUFCMA.writerState_run_lift,
      SUFCMA.writerState_run_set, map_bind, bind_map_left, pure_bind,
      WriterT.run_pure, StateT.run_pure, map_pure, simulateQ_bind,
      simulateQ_pure] at hstep
    obtain ⟨signStep, hsignStep, hstep⟩ := (mem_support_bind_iff _ _ _).1 hstep
    obtain ⟨verifyStep, hverifyStep, hstep⟩ := (mem_support_bind_iff _ _ _).1 hstep
    have hstep' := (mem_support_pure_iff _ _).1 hstep
    subst hstep'
    have hsign : signStep ∈ support ((simulateQ randomOracle
        (Seeded.signFrom secretKey request.epoch request.message signingAttemptLimit 0 :
          OracleComp HashSpec (Option Signature))).run cache) := by
      simpa [xmss, Seeded.sign, romImpl_liftHash] using hsignStep
    obtain ⟨hsignLe, hsignNone, hsignSome⟩ :=
      signFrom_outcome secretKey publicKey keyCache hconsistent hkey request.epoch
        request.message signingAttemptLimit 0 cache hle signStep hsign
    cases hanswer : signStep.1 with
    | none =>
        rw [hanswer] at hverifyStep
        have hverifyPure : verifyStep = (false, signStep.2) := by
          simpa [simulateQ_pure] using hverifyStep
        subst hverifyPure
        refine ⟨fun _ => ⟨request.epoch, request.message, fun trial htrial => ?_⟩,
          hsignLe⟩
        simpa using hsignNone hanswer trial htrial
    | some signature =>
        rw [hanswer] at hverifyStep
        have hverify : verifyStep ∈ support ((simulateQ randomOracle
            (Concrete.verify publicKey request.epoch request.message signature :
              OracleComp HashSpec Bool)).run signStep.2) := by
          simpa [xmss, romImpl_liftHash] using hverifyStep
        obtain ⟨htrue, hfinalLe⟩ := hsignSome signature hanswer verifyStep hverify
        refine ⟨?_, hsignLe.trans hfinalLe⟩
        simp only [htrue, Bool.not_true, Bool.or_false]
        exact hflag.mono (hsignLe.trans hfinalLe)

theorem hashStep_state (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (input : OracleWorld.Domain) (state : QueryLog SigningSpec × Bool) (cache : QueryCache HashSpec) :
    ∀ step ∈ support ((simulateQ romImpl
        ((correctImpl publicKey secretKey (.inl input)).run.run state)).run cache),
      step.1.2 = state ∧ cache ≤ step.2 := by
  intro step hstep
  change step ∈ support ((simulateQ romImpl
    ((liftM (OracleWorld.query input) : CorrectRun _).run.run state)).run cache) at hstep
  rw [SUFCMA.writerState_run_lift, simulateQ_map, StateT.run_map, support_map] at hstep
  obtain ⟨answer, hanswer, rfl⟩ := hstep
  refine ⟨rfl, romImpl_query_cache_le input cache answer ?_⟩
  simpa [simulateQ_spec_query] using hanswer

/-- A run of the correctness experiment's adversary sets the flag only by failing to sign. -/
theorem run_flagExplained (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (signed : QueryLog SigningSpec) (flag : Bool) (cache : QueryCache HashSpec)
    (hle : keyCache ≤ cache) (hflag : FlagExplained secretKey flag cache) :
    ∀ result ∈ support ((simulateQ romImpl
        ((simulateQ (correctImpl publicKey secretKey) computation).run.run (signed, flag))).run
          cache),
      FlagExplained secretKey result.1.2.2 result.2 := by
  induction computation using OracleComp.inductionOn generalizing signed flag cache with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact hflag
  | query_bind input next ih =>
      intro result hresult
      rw [correctRun_query_bind, simulateQ_bind, StateT.run_bind] at hresult
      obtain ⟨step, hstep, hrest⟩ := (mem_support_bind_iff _ _ _).1 hresult
      rw [simulateQ_map, StateT.run_map, support_map] at hrest
      obtain ⟨inner, hinner, rfl⟩ := hrest
      rcases input with t | request
      · obtain ⟨hstate, hcacheLe⟩ := hashStep_state publicKey secretKey t (signed, flag) cache
          step hstep
        rw [hstate] at hinner
        exact ih _ signed flag step.2 (hle.trans hcacheLe) (hflag.mono hcacheLe) inner hinner
      · obtain ⟨hstepFlag, hcacheLe⟩ := signingStep_flagExplained publicKey secretKey keyCache
          hconsistent hkey request signed flag cache hle hflag step hstep
        have hstate : step.1.2 = (step.1.2.1, step.1.2.2) := rfl
        rw [hstate] at hinner
        exact ih _ step.1.2.1 step.1.2.2 step.2 (hle.trans hcacheLe) hstepFlag inner hinner

/-- If a run of the correctness experiment sets the flag, its final cache contains a signing
request whose trials all failed. -/
theorem experiment_flag_signingFails (adversary : Correctness.Adversary OracleWorld PublicKey
      Message Signature lifetime)
    (result : (Bool × ℕ) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl
      (Correctness.experiment xmss adversary)).run ∅))
    (hflag : result.1.1 = true) :
    ∃ parameter seed leafIndex message,
      SigningFails parameter seed leafIndex message result.2 := by
  obtain ⟨output, finalCache⟩ := result
  unfold Correctness.experiment at hresult
  rw [simulateQ_bind, StateT.run_bind] at hresult
  obtain ⟨keys, hkeys, hrest⟩ := (mem_support_bind_iff _ _ _).1 hresult
  obtain ⟨⟨publicKey, secretKey⟩, keysCache⟩ := keys
  have hkeygen : ((publicKey, secretKey), keysCache) ∈
      support ((simulateQ romImpl xmss.keygen).run ∅) := hkeys
  simp only [xmss, simulateQ_bind, StateT.run_bind] at hkeygen
  obtain ⟨seedStep, hseedStep, hkeyStep⟩ := (mem_support_bind_iff _ _ _).1 hkeygen
  have hseedCache : seedStep.2 = ∅ := by
    rw [romImpl_liftM_support] at hseedStep
    obtain ⟨seed, -, hseed⟩ := hseedStep
    rw [← hseed]
  rw [hseedCache, romImpl_liftHash] at hkeyStep
  obtain ⟨keyCache, hprecomputed, hkeyCacheLe, hkey⟩ :=
    seededKeygen_support_precomputed seedStep.1 _ hkeyStep
  have hconsistent := Concrete.precomputedKeygen_support_consistent _ hprecomputed
  simp only [simulateQ_bind, StateT.run_bind] at hrest
  obtain ⟨⟨⟨⟨_unit, requests⟩, ⟨signed, failed⟩⟩, adversaryCache⟩, hadversary, hout⟩ :=
    (mem_support_bind_iff _ _ _).1 hrest
  have hexplained := run_flagExplained publicKey secretKey keyCache hconsistent hkey
    (adversary.main publicKey) [] false keysCache hkeyCacheLe (fun h => by simp at h) _
    hadversary
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hout
  obtain ⟨houtput, hcache⟩ := hout
  simp only at hflag
  rw [houtput] at hflag
  obtain ⟨leafIndex, message, hfails⟩ := hexplained (by simpa using hflag)
  exact ⟨_, _, leafIndex, message, by simpa [hcache] using hfails⟩

/-- The flag is set only if all trials of the request for some public parameter, master seed,
epoch, and message fail. -/
theorem probEvent_flag_le_exists_signingFails
    (adversary : Correctness.Adversary OracleWorld PublicKey Message Signature lifetime) :
    Pr[fun result => result.1.1 = true |
        (simulateQ romImpl (Correctness.experiment xmss adversary)).run ∅] ≤
      Pr[fun result => ∃ parameter seed leafIndex message,
          SigningFails parameter seed leafIndex message result.2 |
        (simulateQ romImpl (Correctness.experiment xmss adversary)).run ∅] := by
  refine probEvent_mono fun result hresult hflag => ?_
  exact experiment_flag_signingFails adversary result hresult hflag

end XmssSecurity.TargetSum.Correct

import XmssSecurity.Proof.Checksum.PrecomputedBoundedSign
import XmssSecurity.Proof.Checksum.OutcomeClassification
import XmssSecurity.Proof.Checksum.Direct.SeedGuessing
import XmssSecurity.Proof.Checksum.Seeded.CacheCoupling
import XmssSecurity.Statement.Security.Correctness
import XmssSecurity.Proof.Common.RepeatedEpochs
import XmssSecurity.Proof.Checksum.Direct.Bridge

/-!
# Correctness of the checksummed scheme

Every signing request is answered by a signature that verifies, whatever the adversary queries:
the correctness error is `0` (`correctnessError_zero`).

Key generation derives the public parameter and the chain starts from the master seed, and then
computes the Merkle tree. The tree computation never queries a seed-derivation input
(`Concrete.treeNode_noSeed`), so it runs as from the empty cache: the key is a key of the
precomputed key generation (`seededKeygen_support_precomputed`), whose secret key agrees with
every larger cache (`Concrete.precomputedKeygen_support_consistent`). A signature is then the
cache-level signature of its encoding, and the cache-level verification accepts it
(`Concrete.CacheReplay.verifyFromCache_signWithEncoding`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Correct

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

/-! ### Signing and verification -/

/-- A signing attempt of the checksummed scheme always returns a signature: every digest decodes.
From any cache above the key's cache, the signature is the cache-level signature of the decoded
encoding. -/
theorem precomputedSignAttempt_replay (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (keyCache initialCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey)
    (step : Option Signature × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ randomOracle
      (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
        OracleComp HashSpec (Option Signature))).run initialCache)) :
    ∃ signature, step.1 = some signature ∧ signature.randomness = randomness ∧
      ∀ largerCache, keyCache ≤ largerCache → step.2 ≤ largerCache →
        ∃ encoding,
          Concrete.CacheView.decodedEncoding largerCache secretKey.parameter leafIndex
              (message, randomness) = some encoding ∧
          signature = Concrete.CacheReplay.signWithEncoding largerCache secretKey leafIndex
            randomness encoding := by
  have hsome : ∃ signature, step.1 = some signature := by
    unfold Concrete.precomputedSignAttempt at hstep
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
    obtain ⟨⟨digest, digestCache⟩, -, hrest⟩ := hstep
    simp only [Checksum.decodeDigest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hrest
    exact ⟨_, by rw [hrest]⟩
  obtain ⟨signature, hsignature⟩ := hsome
  obtain ⟨output, hcached⟩ := Concrete.CacheReplay.precomputedSignAttempt_run_encodingInput_cached
    secretKey leafIndex message randomness initialCache step.2 signature
    (by rw [← hsignature]; exact hstep)
  have hrandomness : signature.randomness = randomness := by
    unfold Concrete.precomputedSignAttempt at hstep
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
    obtain ⟨⟨digest, digestCache⟩, -, hrest⟩ := hstep
    simp only [Checksum.decodeDigest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hrest
    rw [hrest] at hsignature
    simp only [Option.some.injEq] at hsignature
    rw [← hsignature]
    rfl
  refine ⟨signature, hsignature, hrandomness, fun largerCache hkeyLe hle => ?_⟩
  have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) initialCache step.2 largerCache step.1
    hstep hle
  unfold Concrete.precomputedSignAttempt at heval
  simp only [evalWithAnswerFn_bind, Concrete.CacheReplay.eval_encodingHash] at heval
  split at heval
  · rename_i _ encoding hdecode
    simp only [evalWithAnswerFn_pure] at heval
    refine ⟨encoding, ?_, ?_⟩
    · rw [Concrete.CacheView.decodedEncoding_eq_of_cache_eq_some (hle hcached)]
      exact hdecode
    · rw [hsignature, Option.some.injEq] at heval
      rw [← heval]
      exact hconsistent largerCache hkeyLe leafIndex randomness encoding
  · simp [hsignature] at heval

/-- The seeded signer answers a signature, and its verification from the cache after signing,
and every larger cache, accepts. -/
theorem sign_verify (secretKey : Seeded.SecretKey) (publicKey : PublicKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    (leafIndex : LeafIndex) (message : Message) (cache : QueryCache HashSpec)
    (hle : keyCache ≤ cache) :
    ∀ step ∈ support ((simulateQ randomOracle
        (Seeded.sign secretKey leafIndex message : OracleComp HashSpec (Option Signature))).run
          cache),
      cache ≤ step.2 ∧ ∃ signature, step.1 = some signature ∧
        ∀ check ∈ support ((simulateQ randomOracle
            (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool)).run
              step.2),
          check.1 = true ∧ step.2 ≤ check.2 := by
  intro step hstep
  have hcacheLe : cache ≤ step.2 := Concrete.CacheReplay.randomOracle_cache_le _ cache step hstep
  refine ⟨hcacheLe, ?_⟩
  rw [Seeded.sign_eq_signFrom] at hstep
  simp only [signingAttemptLimit, Seeded.signFrom] at hstep
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨⟨randomness, randomnessCache⟩, -, hstep⟩ := hstep
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hstep
  obtain ⟨⟨attempt, attemptCache⟩, hattempt, hrest⟩ := hstep
  obtain ⟨signature, hattemptSome, hrandomness, hreplay⟩ := precomputedSignAttempt_replay
    secretKey.precomputed leafIndex message randomness keyCache randomnessCache hconsistent
    (attempt, attemptCache) hattempt
  simp only at hattemptSome
  subst hattemptSome
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  refine ⟨signature, rfl, fun check hcheck => ?_⟩
  have hfinalLe : attemptCache ≤ check.2 :=
    Concrete.CacheReplay.randomOracle_cache_le _ attemptCache check hcheck
  refine ⟨?_, hfinalLe⟩
  have hverify := Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey leafIndex
    message signature attemptCache check.2 check.1 hcheck
  have hkeyLe : keyCache ≤ check.2 := hle.trans (hcacheLe.trans hfinalLe)
  obtain ⟨encoding, hdecode, hsignature⟩ := hreplay check.2 hkeyLe hfinalLe
  rw [← hverify, hkey check.2 hkeyLe, hsignature]
  exact Concrete.CacheReplay.verifyFromCache_signWithEncoding check.2 secretKey.precomputed
    leafIndex message randomness encoding hdecode

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

/-- One signing query of the correctness experiment keeps the flag `v` at `0`. -/
theorem signingStep_noFailure (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    (request : SignRequest) (signed : QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (hle : keyCache ≤ cache) :
    ∀ step ∈ support ((simulateQ romImpl
        ((correctImpl publicKey secretKey (.inr request)).run.run (signed, false))).run cache),
      step.1.2.2 = false ∧ cache ≤ step.2 := by
  intro step hstep
  change step ∈ support ((simulateQ romImpl
    ((Correctness.signingOracle xmss publicKey secretKey request).run.run (signed, false))).run
      cache) at hstep
  unfold Correctness.signingOracle at hstep
  simp only [WriterT.run_bind, StateT.run_bind, StateT.run_map, AddWriterT.run_addTell,
    SUFCMA.writerState_run_get, pure_bind, StateT.run_pure] at hstep
  split at hstep
  · simp only [WriterT.run_pure, StateT.run_pure, map_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hstep
    subst hstep
    exact ⟨rfl, le_rfl⟩
  · simp only [WriterT.run_bind, StateT.run_bind, SUFCMA.writerState_run_lift,
      SUFCMA.writerState_run_set, map_bind, bind_map_left, Functor.map_map, pure_bind,
      WriterT.run_pure, StateT.run_pure, map_pure, simulateQ_bind, simulateQ_map,
      simulateQ_pure, StateT.run_map] at hstep
    obtain ⟨signStep, hsignStep, hstep⟩ := (mem_support_bind_iff _ _ _).1 hstep
    obtain ⟨verifyStep, hverifyStep, hstep⟩ := (mem_support_bind_iff _ _ _).1 hstep
    have hstep' := (mem_support_pure_iff _ _).1 hstep
    subst hstep'
    have hsign : signStep ∈ support ((simulateQ randomOracle
        (Seeded.sign secretKey request.epoch request.message :
          OracleComp HashSpec (Option Signature))).run cache) := by
      simpa [xmss, romImpl_liftHash] using hsignStep
    obtain ⟨hcacheLe, signature, hsome, hverifyAll⟩ :=
      sign_verify secretKey publicKey keyCache hconsistent hkey request.epoch request.message
        cache hle signStep hsign
    rw [hsome] at hverifyStep
    have hverify : verifyStep ∈ support ((simulateQ randomOracle
        (Concrete.verify publicKey request.epoch request.message signature :
          OracleComp HashSpec Bool)).run signStep.2) := by
      simpa [xmss, romImpl_liftHash] using hverifyStep
    obtain ⟨htrue, hfinalLe⟩ := hverifyAll verifyStep hverify
    exact ⟨by simp [htrue], hcacheLe.trans hfinalLe⟩

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

/-- No signing query of the correctness experiment sets the flag `v`. -/
theorem run_noFailure (publicKey : PublicKey) (secretKey : Seeded.SecretKey)
    (keyCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keyCache secretKey.precomputed)
    (hkey : ∀ largerCache, keyCache ≤ largerCache →
      publicKey = Concrete.CacheReplay.publicKeyFromCache largerCache secretKey.precomputed)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (signed : QueryLog SigningSpec) (cache : QueryCache HashSpec) (hle : keyCache ≤ cache) :
    ∀ result ∈ support ((simulateQ romImpl
        ((simulateQ (correctImpl publicKey secretKey) computation).run.run (signed, false))).run
          cache),
      result.1.2.2 = false := by
  induction computation using OracleComp.inductionOn generalizing signed cache with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, WriterT.run_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      rw [hresult]
  | query_bind input next ih =>
      intro result hresult
      rw [correctRun_query_bind, simulateQ_bind, StateT.run_bind] at hresult
      obtain ⟨step, hstep, hrest⟩ := (mem_support_bind_iff _ _ _).1 hresult
      rw [simulateQ_map, StateT.run_map, support_map] at hrest
      obtain ⟨inner, hinner, rfl⟩ := hrest
      rcases input with t | request
      · obtain ⟨hstate, hcacheLe⟩ := hashStep_state publicKey secretKey t (signed, false) cache
          step hstep
        rw [hstate] at hinner
        exact ih _ signed step.2 (hle.trans hcacheLe) inner hinner
      · obtain ⟨hflag, hcacheLe⟩ := signingStep_noFailure publicKey secretKey keyCache hconsistent
          hkey request signed cache hle step hstep
        have hstate : step.1.2 = (step.1.2.1, false) := Prod.ext rfl hflag
        rw [hstate] at hinner
        exact ih _ step.1.2.1 step.2 (hle.trans hcacheLe) inner hinner

/-- The checksummed scheme has correctness error `0`: whatever the adversary queries, every
signing request is answered by a signature that verifies. -/
theorem correctnessError_zero : Correctness.HasCorrectnessError xmss 0 := by
  intro q adversary _
  rw [zero_mul, nonpos_iff_eq_zero]
  unfold Correctness.advantage Correctness.game RandomOracleModel.run
  rw [probEvent_eq_zero_iff]
  intro result hresult
  rw [← Security.romImpl_eq, StateT.run'_eq, support_map] at hresult
  obtain ⟨⟨output, finalCache⟩, hrun, rfl⟩ := hresult
  unfold Correctness.experiment at hrun
  rw [simulateQ_bind, StateT.run_bind] at hrun
  obtain ⟨keys, hkeys, hrest⟩ := (mem_support_bind_iff _ _ _).1 hrun
  obtain ⟨⟨publicKey, secretKey⟩, keysCache⟩ := keys
  -- key generation
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
  -- the adversary's run
  simp only [simulateQ_bind, StateT.run_bind] at hrest
  obtain ⟨⟨⟨⟨unit, requests⟩, ⟨signed, failed⟩⟩, adversaryCache⟩, hadversary, hout⟩ :=
    (mem_support_bind_iff _ _ _).1 hrest
  have hfailed := run_noFailure publicKey secretKey keyCache hconsistent hkey
    (adversary.main publicKey) [] keysCache hkeyCacheLe _ hadversary
  simp only at hfailed
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hout
  rw [hout.1, hfailed]
  simp

end XmssSecurity.Checksum.Correct

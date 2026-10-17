import XmssSecurity.Proof.Checksum.Direct.Basic
import XmssSecurity.Proof.Checksum.Deterministic.ReferenceDistribution
import XmssSecurity.Proof.Checksum.ConcreteQueryBound

/-!
# Seed guessing charged to the adversary's direct hash queries

Only inputs whose tweak tag byte is `0`, `5` or `7` (`MaySeedHit`) can be seed derivations. The
key-generation tree, the table signer and verification only query tags `1`–`4`, so in the table
game the only `MaySeedHit` queries are the adversary's direct hash queries. This sharpens
`forgeAdvantage_deterministic_le_reference` to a loss of `D / 2^256` for an adversary with at most
`D` direct hash queries (`forgeAdvantage_deterministic_le_reference_direct`), and shows that
`memoAdversary` preserves the direct-query bound (`memoAdversary_isDirectQueryBound`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum

/-- Inputs whose tweak tag byte is `0`, `5` or `7`: the tags of the seed derivations. -/
def MaySeedHit (input : HashInput) : Prop :=
  input[1]? = some 0 ∨ input[1]? = some 5 ∨ input[1]? = some 7

instance : DecidablePred MaySeedHit := fun input =>
  inferInstanceAs (Decidable (input[1]? = some 0 ∨ input[1]? = some 5 ∨ input[1]? = some 7))

theorem not_maySeedHit_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : ¬MaySeedHit (tweakableHashInput parameter domain payload) := by
  cases domain <;>
    simp [MaySeedHit, tweakableHashInput, tweakBytes, fieldBytes, hashDomainFields, tweakFields,
      bytesLE, protocolDomainSep] <;> decide

theorem maySeedHit_keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : MaySeedHit (keygenHashInput parameter domain seed) := by
  cases domain <;>
    simp [MaySeedHit, keygenHashInput, keygenDomainFields, fieldBytes, tweakFields,
      bytesLE, protocolDomainSep]

theorem maySeedHit_randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) :
    MaySeedHit (randomizerHashInput parameter seed leafIndex message trial) := by
  simp [MaySeedHit, randomizerHashInput, fieldBytes, bytesLE, protocolDomainSep]

/-! ## Honest hash computations make no seed-shaped query -/

namespace Concrete

theorem tweakableHash_noSeed (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      MaySeedHit 0 := by
  simp [tweakableHash, oracleHash, not_maySeedHit_tweakableHashInput]

theorem chainWalk_noSeed (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP MaySeedHit 0 := by
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      rw [chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact tweakableHash_noSeed _ _ _
      · simp

theorem leafAt_noSeed (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    (leafAt parameter secret leafIndex : OracleComp HashSpec Digest).IsQueryBoundP MaySeedHit 0 := by
  rw [leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (sequenceFin_queryBound_zero _ _ fun chain => chainWalk_noSeed _ _ _ _ _ _) ?_
  intro endpoints _
  exact tweakableHash_noSeed _ _ _

theorem treeNode_noSeed (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    (treeNode parameter secret levels node : OracleComp HashSpec Digest).IsQueryBoundP
      MaySeedHit 0 := by
  induction levels generalizing node with
  | zero =>
      rw [treeNode_zero_eq]
      exact leafAt_noSeed _ _ _
  | succ levels ih =>
      rw [treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro right _
      split
      · exact tweakableHash_noSeed _ _ _
      · simp

theorem encodingHash_noSeed (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (encodingHash parameter leafIndex message randomness : OracleComp HashSpec Digest).IsQueryBoundP
      MaySeedHit 0 :=
  tweakableHash_noSeed _ _ _

theorem authenticationRoot_noSeed (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (levels : Nat) (leaf : Digest) :
    (authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP MaySeedHit 0 := by
  induction levels with
  | zero => simp [authenticationRoot]
  | succ levels ih =>
      rw [authenticationRoot]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro current _
      unfold authenticationNodeHash
      split
      · split
        · exact tweakableHash_noSeed _ _ _
        · exact tweakableHash_noSeed _ _ _
      · simp

theorem verifyAfterLeaf_noSeed (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool).IsQueryBoundP
      MaySeedHit 0 := by
  unfold verifyAfterLeaf
  generalize treeHeight = n
  exact OracleComp.isQueryBoundP_bind (m := 0)
    (authenticationRoot_noSeed publicKey.parameter leafIndex signature n leaf)
    (fun _ _ => OracleComp.isQueryBoundP_pure _ _ _)

theorem verify_noSeed (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (verify publicKey leafIndex message signature : OracleComp HashSpec Bool).IsQueryBoundP
      MaySeedHit 0 := by
  rw [verify_eq_decode]
  refine OracleComp.isQueryBoundP_bind (m := 0) (encodingHash_noSeed _ _ _ _) ?_
  intro digest _
  split
  · refine OracleComp.isQueryBoundP_bind (m := 0)
      (sequenceFin_queryBound_zero _ _ fun chain => chainWalk_noSeed _ _ _ _ _ _) ?_
    intro endpoints _
    refine OracleComp.isQueryBoundP_bind (m := 0) (tweakableHash_noSeed _ _ _) ?_
    intro leaf _
    exact verifyAfterLeaf_noSeed _ _ _ _
  · exact OracleComp.isQueryBoundP_pure _ _ _

theorem precomputedSignAttempt_noSeed (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) :
    (precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP MaySeedHit 0 := by
  rw [precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (m := 0) (encodingHash_noSeed _ _ _ _) ?_
  intro digest _
  split <;> simp

end Concrete

end XmssSecurity.Checksum

namespace XmssSecurity.Checksum.Seeded

theorem tableSignFrom_noSeed (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.Checksum.SecretKey)
    (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    (tableSignFrom randomizers secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP MaySeedHit 0 := by
  induction attempts generalizing trial with
  | zero => simp [tableSignFrom]
  | succ attempts ih =>
      rw [tableSignFrom]
      refine OracleComp.isQueryBoundP_bind (m := 0) (Concrete.precomputedSignAttempt_noSeed _ _ _ _) ?_
      intro attempt _
      cases attempt with
      | none => exact ih _
      | some signature => simp

theorem tableSign_noSeed (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.Checksum.SecretKey)
    (leafIndex : LeafIndex) (message : Message) :
    (tableSign randomizers secretKey leafIndex message :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP MaySeedHit 0 :=
  tableSignFrom_noSeed _ _ _ _ _ _

end XmssSecurity.Checksum.Seeded

namespace XmssSecurity.Checksum.Seeded

open DeterministicSigning

theorem memoize_isQueryBoundP {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache SigningSpec) (D : ℕ)
    (h : computation.IsQueryBoundP Direct.IsDirectHashQuery D) :
    (memoize computation cache).IsQueryBoundP Direct.IsDirectHashQuery D := by
  induction computation using OracleComp.inductionOn generalizing cache D with
  | pure value => simp [memoize_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [memoize_base, isQueryBoundP_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer cache _ (h.2 answer)⟩
      | inr request =>
          rw [memoize_request]
          have hnot : ¬Direct.IsDirectHashQuery (.inr request) := Direct.not_isDirectHashQuery_sign request
          cases hc : cache request with
          | some answer => simpa [hnot] using ih answer cache D (by simpa [hnot] using h.2 answer)
          | none =>
              rw [isQueryBoundP_query_bind_iff]
              refine ⟨Or.inl hnot, fun answer => ?_⟩
              simpa [hnot] using ih answer _ D (by simpa [hnot] using h.2 answer)

theorem memoAdversary_isDirectQueryBound (adversary : Adversary) (D : ℕ)
    (h : Direct.IsDirectQueryBound adversary D) :
    Direct.IsDirectQueryBound (memoAdversary adversary) D :=
  fun publicKey => memoize_isQueryBoundP _ ∅ D (h publicKey)

end XmssSecurity.Checksum.Seeded

namespace XmssSecurity.Checksum.Seeded

/-! ## Seed-shaped queries of the table game -/

theorem isQueryBoundP_simulateQ_writer_run {ι κ : Type} {source : OracleSpec ι}
    {target : OracleSpec κ} {α : Type}
    (impl : QueryImpl source (WriterT (QueryLog SigningSpec) (OracleComp target)))
    (p : ι → Prop) [DecidablePred p] (q : κ → Prop) [DecidablePred q]
    (hstep : ∀ t, ((impl t).run).IsQueryBoundP q (if p t then 1 else 0))
    (computation : OracleComp source α) (n : ℕ) (h : computation.IsQueryBoundP p n) :
    ((simulateQ impl computation).run).IsQueryBoundP q n := by
  induction computation using OracleComp.inductionOn generalizing n with
  | pure value => simp
  | query_bind t next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_query_bind, WriterT.run_bind]
      have hn : (if p t then 1 else 0) + (if p t then n - 1 else n) = n := by
        rcases h.1 with hp | hp <;> split_ifs <;> omega
      rw [← hn]
      refine OracleComp.isQueryBoundP_bind (hstep t) (fun x _ => ?_)
      exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (ih x.1 _ (h.2 x.1))

theorem liftM_hash_noSeed {α : Type} (computation : OracleComp HashSpec α)
    (h : computation.IsQueryBoundP MaySeedHit 0) :
    (liftM computation : OracleComp OracleWorld α).IsQueryBoundP (hashBad MaySeedHit) 0 :=
  OracleComp.IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) h

theorem tableGameImpl_step (randomizers : RandomizerOutputs) (sk : XmssSecurity.Checksum.SecretKey)
    (t : (OracleWorld + SigningSpec).Domain) :
    (((forwardOracles + signingOracle (tableScheme randomizers) sk) t).run).IsQueryBoundP
      (hashBad MaySeedHit) (if Direct.IsDirectHashQuery t then 1 else 0) := by
  rcases t with (t | t) | request
  · change ((fun a => (a, (∅ : QueryLog SigningSpec))) <$>
      (liftM (OracleWorld.query (.inl t)) : OracleComp OracleWorld _)).IsQueryBoundP _ _
    rw [OracleComp.isQueryBoundP_map_iff]
    simp [hashBad]
  · change ((fun a => (a, (∅ : QueryLog SigningSpec))) <$>
      (liftM (OracleWorld.query (.inr t)) : OracleComp OracleWorld _)).IsQueryBoundP _ _
    rw [OracleComp.isQueryBoundP_map_iff]
    simp [hashBad]
  · simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply]
    simp
    exact liftM_hash_noSeed _ (tableSign_noSeed _ _ _ _)

theorem tableGameRest_bound (randomizers : RandomizerOutputs) (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (pk : PublicKey) (sk : XmssSecurity.Checksum.SecretKey) :
    (gameRest (tableScheme randomizers) adversary pk sk).IsQueryBoundP (hashBad MaySeedHit) D := by
  unfold gameRest
  rw [← Nat.add_zero D]
  refine OracleComp.isQueryBoundP_bind
    (isQueryBoundP_simulateQ_writer_run _ Direct.IsDirectHashQuery _
      (tableGameImpl_step randomizers sk) _ D (hD pk)) ?_
  rintro ⟨forgery, log⟩ _
  rw [← Nat.add_zero 0]
  refine OracleComp.isQueryBoundP_bind
    (liftM_hash_noSeed _ (Concrete.verify_noSeed _ _ _ _)) ?_
  intro verified _
  simp

theorem tableGameAfterSecrets_bound (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (parameter : PublicParameter)
    (secret : ChainSecrets) (randomizers : RandomizerOutputs) :
    (tableGameAfterSecrets adversary parameter secret randomizers).IsQueryBoundP
      (hashBad MaySeedHit) D := by
  unfold tableGameAfterSecrets
  rw [← Nat.zero_add D]
  refine OracleComp.isQueryBoundP_bind (liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_bound randomizers adversary D hD _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Concrete.treeNode_noSeed _ _ _ _

theorem traceHashes_filter_length_le {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (D : ℕ)
    (h : computation.IsQueryBoundP (hashBad MaySeedHit) D) (result : α × List HashInput)
    (hresult : result ∈ support ((simulateQ romImpl (traceHashes computation)).run' cache)) :
    (result.2.filter (fun input => decide (MaySeedHit input))).length ≤ D := by
  induction computation using OracleComp.inductionOn generalizing cache D result with
  | pure value =>
      rw [traceHashes_pure] at hresult
      simp at hresult
      subst hresult
      simp
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [traceHashes_query_bind, run'_query_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨first, _, hrest⟩ := hresult
      simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
        Functor.map_map, support_map, Set.mem_image] at hrest
      obtain ⟨⟨rest, finalCache⟩, hmem, rfl⟩ := hrest
      have hbound := ih first.1 first.2 _ (h.2 first.1) rest (by
        rw [StateT.run'_eq, support_map]
        exact ⟨(rest, finalCache), hmem, rfl⟩)
      rcases input with input | input
      · simpa [prependHash, hashBad] using hbound
      · by_cases hmay : MaySeedHit input
        · have hpos : 0 < D := h.1.resolve_left (by simpa [hashBad] using hmay)
          simp only [hashBad, hmay, if_true] at hbound
          simp [prependHash, hmay]
          omega
        · simpa [prependHash, hashBad, List.filter_cons, hmay] using hbound

/-! ## Seed guessing charged to seed-shaped queries only -/

/-- A query that names the seed and carries a seed-derivation tag. -/
def DerivationHit (seed : MasterSeed) (input : HashInput) : Prop :=
  SeedHit input seed ∧ MaySeedHit input

theorem probEvent_traceHits_derivationHit_le (inputs : List HashInput) :
    Pr[fun seed => TraceHits (DerivationHit seed) inputs | sampleMasterSeed] ≤
      (inputs.filter (fun input => decide (MaySeedHit input))).length /
        ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  refine (probEvent_mono ?_).trans
    (probEvent_seedHitLog_le (inputs.filter (fun input => decide (MaySeedHit input))))
  rintro seed _ ⟨input, hinput, hseed, hmay⟩
  exact ⟨input, List.mem_filter.mpr ⟨hinput, by simpa using hmay⟩, hseed⟩

open scoped Classical in
theorem probOutput_stopBefore_derivationHit_le {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (D : ℕ)
    (hbound : computation.IsQueryBoundP (hashBad MaySeedHit) D) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (stopBefore (hashBad (DerivationHit seed)) computation)).run' cache] ≤
        D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let trace := (simulateQ romImpl (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceHits (DerivationHit seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map,
        decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (TraceHits (DerivationHit seed) result.2)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (probEvent_traceHits_derivationHit_le result.2).trans
        (ENNReal.div_le_div
          (by exact_mod_cast traceHashes_filter_length_le computation cache D hbound result hresult)
          le_rfl)

open scoped Classical in
theorem probEvent_random_cache_change_derivationHit_le {α : Type}
    (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (DerivationHit seed) (initial seed) cache)
    (D : ℕ) (hbound : computation.IsQueryBoundP (hashBad MaySeedHit) D) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ romImpl computation).run' (initial seed)] ≤
      Pr[event | (simulateQ romImpl computation).run' cache] + D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  let stopped := fun seed =>
    (simulateQ romImpl (stopBefore (hashBad (DerivationHit seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ romImpl computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le (DerivationHit seed)
          computation (initial seed) cache (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add (le_refl (Pr[event | (simulateQ romImpl computation).run' cache]))
        (probOutput_stopBefore_derivationHit_le computation cache D hbound)

theorem signingDerivationCache_agreeOutside_derivationHit (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    AgreeOutside (DerivationHit seed)
      (signingDerivationCache seed parameterOutput outputs randomizers) ∅ := by
  intro input hinput
  unfold signingDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · unfold derivationCache
    rw [cacheRows_apply_of_not_mem]
    · apply QueryCache.cacheQuery_of_ne
      intro h
      exact hinput (h.symm ▸ ⟨derivationSeedHit_keygen 0 .parameter seed,
        maySeedHit_keygenHashInput 0 .parameter seed⟩)
    · intro leafIndex chain h
      exact hinput (h.symm ▸ ⟨derivationSeedHit_keygen (truncateHash parameterOutput)
        (.chain leafIndex chain) seed,
        maySeedHit_keygenHashInput (truncateHash parameterOutput) (.chain leafIndex chain) seed⟩)
  · intro position heq
    exact hinput (heq.symm ▸ ⟨derivationSeedHit_randomizer (truncateHash parameterOutput) seed
      position.1.epoch position.1.message position.2,
      maySeedHit_randomizerHashInput (truncateHash parameterOutput) seed
        position.1.epoch position.1.message position.2⟩)

theorem forgeAdvantage_deterministic_le_table_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    forgeAdvantage scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | drawSigningMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | drawSigningMaterial >>= fun material =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_derivationHit_le _
    (fun seed => signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
    (fun seed => signingDerivationCache_agreeOutside_derivationHit seed _ _ _) D
    (tableGameAfterSecrets_bound adversary D hD _ _ _) (fun value => value = true)

theorem forgeAdvantage_deterministic_le_reference_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table_direct adversary D hD).trans (add_le_add hmemo le_rfl)

end XmssSecurity.Checksum.Seeded

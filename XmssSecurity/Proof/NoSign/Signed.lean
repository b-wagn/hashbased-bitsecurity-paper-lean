import XmssSecurity.Proof.NoSign.HiddenSibling
import XmssSecurity.Proof.NoSign.Proportional

/-!
# The hidden top sibling for an adversary that may sign

On the executions without a signing request, any adversary runs as with every oracle forwarded
(`Proportional.lean`). Its forged top sibling is then the honest one with probability at most
`(1 + N) / 2^128` on average, where `N` is the expected number of inputs its forwarded run caches
from the empty cache (`hiddenSibling_unsigned_le`); `N` is at most the expected number of direct
hash queries of the forwarded run (`idealSize_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.NoSign

/-! ## Cache sizes -/

/-- The number of cached inputs. -/
noncomputable def cacheSize (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' input, if cache input ≠ none then 1 else 0

theorem cacheSize_empty : cacheSize ∅ = 0 := by
  simp [cacheSize]

theorem cacheSize_cacheQuery_le (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) : cacheSize (cache.cacheQuery input output) ≤ cacheSize cache + 1 := by
  unfold cacheSize
  calc
    _ ≤ ∑' candidate, ((if cache candidate ≠ none then 1 else 0 : ℝ≥0∞) +
          if candidate = input then 1 else 0) := by
      refine ENNReal.tsum_le_tsum fun candidate => ?_
      by_cases heq : candidate = input
      · subst candidate
        simp
      · rw [QueryCache.cacheQuery_of_ne _ _ heq]
        simp [heq]
    _ = _ := by rw [ENNReal.tsum_add, tsum_ite_eq]

theorem romImpl_cacheSize_le (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) :
    cacheSize result.2 ≤ cacheSize cache + if IsWorldHashQuery input then 1 else 0 := by
  rcases input with uniformIndex | hashInput
  · have hcache : result.2 = cache := by
      simp [romImpl, unifFwdImpl, QueryImpl.liftTarget_apply,
        HasQuery.toQueryImpl_apply] at hresult
      obtain ⟨_, rfl⟩ := hresult
      rfl
    rw [hcache]
    exact le_self_add
  · simp only [IsWorldHashQuery, if_true]
    change result ∈ support ((randomOracle (spec := HashSpec) hashInput).run cache) at hresult
    cases hnone : cache hashInput with
    | some output =>
        rw [QueryImpl.withCaching_run_some _ hnone, support_pure,
          Set.mem_singleton_iff] at hresult
        rw [hresult]
        exact le_self_add
    | none =>
        rw [QueryImpl.withCaching_run_none _ hnone, support_map] at hresult
        obtain ⟨output, _, rfl⟩ := hresult
        exact cacheSize_cacheQuery_le cache hashInput output

/-- The expected number of inputs the adversary's forwarded run caches from the empty cache. -/
noncomputable def idealSize (adversary : Adversary) (publicKey : PublicKey) : ℝ≥0∞ :=
  ∑' result, Pr[= result | idealRun adversary publicKey] * cacheSize result.2

theorem idealSize_le (adversary : Adversary) (publicKey : PublicKey) :
    idealSize adversary publicKey ≤
      expectedSimulatedQueryCount romImpl IsWorldHashQuery (forwardPhase adversary publicKey) ∅ := by
  have h := expectedResource_le_initial_add_expectedSimulatedQueryCount romImpl IsWorldHashQuery
    cacheSize (fun input cache result hresult => romImpl_cacheSize_le input cache result hresult)
    (forwardPhase adversary publicKey) ∅
  rwa [cacheSize_empty, zero_add] at h

/-! ## The forwarded run, counted at the adversary's level -/

/-- The forwarded run as an implementation of the adversary's actions. -/
noncomputable def idealImpl :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) ProbComp) :=
  fun input => simulateQ romImpl (forwardOnly input)

theorem expectedWorldHash_forwardOnly_eq {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl IsWorldHashQuery (simulateQ forwardOnly computation)
        cache =
      expectedSimulatedQueryCount idealImpl Direct.IsDirectHashQuery computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_query_bind]
      rcases input with world | request
      · change expectedSimulatedQueryCount romImpl IsWorldHashQuery
            (liftM (OracleWorld.query world) >>= fun answer =>
              simulateQ forwardOnly (next answer)) cache = _
        rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
        simp_rw [ih]
        have hstep : (idealImpl (.inl world)).run cache = (romImpl world).run cache := by
          simp only [idealImpl, forwardOnly, forwardWorld, QueryImpl.add_apply_inl,
            simulateQ_spec_query]
        rw [hstep]
        rcases world with uniformIndex | hashInput <;> simp [IsWorldHashQuery]
      · change expectedSimulatedQueryCount romImpl IsWorldHashQuery
            (pure none >>= fun answer => simulateQ forwardOnly (next answer)) cache = _
        rw [pure_bind, expectedSimulatedQueryCount_query_bind]
        have hstep : (idealImpl (.inr request)).run cache = pure (none, cache) := by
          simp only [idealImpl, forwardOnly, refuseSigning, QueryImpl.add_apply_inr,
            simulateQ_pure, StateT.run_pure]
        rw [hstep, tsum_probOutput_pure_mul, ih]
        simp

theorem romImpl_uniformFaithful (n : ℕ) (cache : QueryCache HashSpec) :
    (romImpl (.inl n)).run cache =
      (fun sample => (sample, cache)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp [romImpl, unifFwdImpl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]

theorem idealImpl_uniformFaithful : UniformFaithful idealImpl := fun n cache => by
  simp only [idealImpl, forwardOnly, forwardWorld, QueryImpl.add_apply_inl, simulateQ_spec_query]
  exact romImpl_uniformFaithful n cache

theorem mappedImpl_uniformFaithful (publicKey : PublicKey) (secretKey : SecretKey) :
    UniformFaithful (cappedUnloggedMappedAdversaryImpl publicKey secretKey) := fun n cache =>
  romImpl_uniformFaithful n cache

/-! ## A union bound and the public-key marginal -/

theorem probEvent_exists_le_tsum {α β : Type} (computation : ProbComp α)
    (event : β → α → Prop) :
    Pr[fun a => ∃ b, event b a | computation] ≤ ∑' b, Pr[event b | computation] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hexists
  · obtain ⟨b, hb⟩ := hexists
    exact (by simp [hb] : Pr[= a | computation] ≤ if event b a then Pr[= a | computation] else 0)
      |>.trans (ENNReal.le_tsum (f := fun b => if event b a then Pr[= a | computation] else 0) b)
  · exact zero_le

/-- An average over the public key of key generation. -/
noncomputable def publicKeyAverage (value : PublicKey → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' parameter, Pr[= parameter | Concrete.samplePublicParameter] *
    ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      value ⟨truncateHash output, parameter⟩

theorem tsum_probOutput_mul_const {α : Type} (computation : ProbComp α) (value : ℝ≥0∞) :
    ∑' a, Pr[= a | computation] * value = value := by
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

theorem tsum_keygen_publicKey (value : PublicKey → ℝ≥0∞) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
        value keyResult.1.1 = publicKeyAverage value := by
  rw [keygen_run_eq, tsum_probOutput_bind_mul]
  unfold publicKeyAverage
  refine tsum_congr fun parameter => congrArg _ ?_
  rw [tsum_probOutput_bind_mul]
  refine (tsum_congr fun secret => congrArg _ ?_).trans (tsum_probOutput_mul_const _ _)
  rw [tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_pure_mul]
  have hdist := evalDist_rootTree_split parameter secret
  rw [show (∑' tree, Pr[= tree | (simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest)).run ∅] * value ⟨tree.1, parameter⟩) =
      ∑' tree, Pr[= tree | (do
        let left ← (simulateQ randomOracle
          (Concrete.treeNode parameter secret (treeHeight - 1)
            (Concrete.childNode Concrete.rootNode false) : OracleComp HashSpec Digest)).run ∅
        let right ← (simulateQ randomOracle
          (Concrete.treeNode parameter secret (treeHeight - 1)
            (Concrete.childNode Concrete.rootNode true) : OracleComp HashSpec Digest)).run left.2
        let output ← $ᵗ HashOutput
        pure (truncateHash output,
          right.2.cacheQuery (topInput parameter left.1 right.1) output))] *
        value ⟨tree.1, parameter⟩
    from tsum_congr fun tree => by rw [probOutput_congr rfl hdist]]
  rw [tsum_probOutput_bind_mul]
  refine (tsum_congr fun left => congrArg _ ?_).trans (tsum_probOutput_mul_const _ _)
  rw [tsum_probOutput_bind_mul]
  refine (tsum_congr fun right => congrArg _ ?_).trans (tsum_probOutput_mul_const _ _)
  rw [tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_pure_mul]

theorem tsum_scheme_keygen_publicKey (value : PublicKey → ℝ≥0∞) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        value keyResult.1.1 = publicKeyAverage value := by
  have hdist : 𝒟[(simulateQ romImpl Concrete.scheme.keygen).run ∅] =
      𝒟[Concrete.materializeCachedKeyResult <$> (simulateQ romImpl Concrete.keygen).run ∅] := by
    rw [Concrete.evalDist_materialized_keygen_eq_precomputedKeygen]
    rfl
  rw [← tsum_keygen_publicKey, show (∑' keyResult, Pr[= keyResult |
      (simulateQ romImpl Concrete.scheme.keygen).run ∅] * value keyResult.1.1) =
      ∑' keyResult, Pr[= keyResult | Concrete.materializeCachedKeyResult <$>
        (simulateQ romImpl Concrete.keygen).run ∅] * value keyResult.1.1 from
    tsum_congr fun keyResult => by rw [probOutput_congr rfl hdist], tsum_probOutput_map_mul]
  rfl

/-! ## The hidden sibling on the executions without a request -/

theorem probEvent_subtrees_ideal_le_size (parameter : PublicParameter) (output : HashOutput)
    (forgery : Forgery) (finalCache : QueryCache HashSpec) :
    Pr[fun sample =>
        HiddenSiblingGuessed (splitCache parameter sample output)
          (SecretKey.withoutPrecomputation parameter sample.1) forgery ∨
        HitsCache (splitCache parameter sample output) finalCache | subtrees parameter] ≤
      digestInverse * (1 + cacheSize finalCache) := by
  classical
  calc
    _ ≤ Pr[fun sample => honestSibling (splitCache parameter sample output) parameter sample.1
            forgery.epoch = forgery.signature.authPath topLevel | subtrees parameter] +
          Pr[fun sample => ∃ input, finalCache input ≠ none ∧
            splitCache parameter sample output input ≠ none | subtrees parameter] := by
      refine (probEvent_mono fun sample _ hevent => ?_).trans (probEvent_or_le _ _ _)
      rcases hevent with hguess | ⟨input, hfinal, hcached⟩
      · exact Or.inl hguess.symm
      · exact Or.inr ⟨input, hfinal, hcached⟩
    _ ≤ digestInverse + ∑' input, if finalCache input ≠ none then digestInverse else 0 := by
      refine add_le_add (probEvent_subtrees_honestSibling_le parameter output forgery.epoch _)
        ((probEvent_exists_le_tsum _ _).trans (ENNReal.tsum_le_tsum fun input => ?_))
      split_ifs with hfinal
      · exact (probEvent_mono fun _ _ h => h.2).trans
          (probEvent_subtrees_cached_le parameter output input)
      · exact le_of_eq (probEvent_eq_zero fun _ _ h => hfinal h.1)
    _ = digestInverse * (1 + cacheSize finalCache) := by
      rw [mul_add, mul_one, cacheSize, ← ENNReal.tsum_mul_left]
      congr 1
      exact tsum_congr fun input => by split_ifs <;> simp

/-- The forged top sibling of the forwarded run is the honest one with probability at most
`(1 + N) / 2^128` on average over the public key, where `N` is the expected number of inputs the
forwarded run caches from the empty cache. -/
theorem hiddenSibling_forward_le (adversary : Adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
      Pr[fun result : Forgery × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 |
        (simulateQ romImpl (forwardPhase adversary keyResult.1.1)).run keyResult.2] ≤
      digestInverse * publicKeyAverage fun publicKey => 1 + idealSize adversary publicKey := by
  let event : (PublicKey × SecretKey) × QueryCache HashSpec →
      Forgery × QueryCache HashSpec → Prop := fun keyResult result =>
    HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 ∨ HitsCache keyResult.2 result.2
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
          Pr[event keyResult | idealRun adversary keyResult.1.1] :=
      ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (probEvent_run_le_empty (forwardPhase adversary keyResult.1.1) keyResult.2
          (HiddenSiblingGuessed keyResult.2 keyResult.1.2))
    _ = Pr[fun joint => event joint.1 joint.2 |
          (simulateQ romImpl Concrete.keygen).run ∅ >>= fun keyResult =>
            (fun result => (keyResult, result)) <$> idealRun adversary keyResult.1.1] := by
      rw [probEvent_bind_eq_tsum]
      refine tsum_congr fun keyResult => ?_
      rw [probEvent_map]
      rfl
    _ ≤ _ := by
      rw [keygen_run_eq]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum]
      unfold publicKeyAverage
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun parameter => ?_
      rw [mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      let keyOf : (LeafIndex → ChainIndex → Digest) → Digest × QueryCache HashSpec →
          (PublicKey × SecretKey) × QueryCache HashSpec := fun secret tree =>
        ((⟨tree.1, parameter⟩, SecretKey.withoutPrecomputation parameter secret), tree.2)
      let observed : ProbComp (HashOutput × (Forgery × QueryCache HashSpec)) := do
        let output ← $ᵗ HashOutput
        let result ← idealRun adversary ⟨truncateHash output, parameter⟩
        pure (output, result)
      let finish : ((LeafIndex → ChainIndex → Digest) ×
          (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec)) →
          HashOutput × (Forgery × QueryCache HashSpec) →
          ((PublicKey × SecretKey) × QueryCache HashSpec) × (Forgery × QueryCache HashSpec) :=
        fun sample seen =>
          (keyOf sample.1 (truncateHash seen.1, splitCache parameter sample seen.1), seen.2)
      have hsplit :
          𝒟[Concrete.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealRun adversary (keyOf secret tree).1.1] =
          𝒟[subtrees parameter >>= fun sample => observed >>= fun seen =>
            pure (finish sample seen)] := by
        have hkeygen : (Concrete.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealRun adversary (keyOf secret tree).1.1) =
            keygenTree parameter >>= fun sampled =>
              (fun result => (keyOf sampled.1 sampled.2, result)) <$>
                idealRun adversary ⟨sampled.2.1, parameter⟩ := by
          simp only [keygenTree, bind_assoc, pure_bind]
          rfl
        rw [hkeygen, evalDist_bind, evalDist_keygenTree_split, ← evalDist_bind]
        simp only [observed, finish, keyOf, bind_assoc, map_eq_bind_pure_comp, pure_bind,
          Function.comp_apply]
        rfl
      rw [probEvent_congr' (fun _ _ => Iff.rfl) hsplit, probEvent_bind_bind_swap,
        probEvent_bind_eq_tsum]
      calc
        _ ≤ ∑' seen, Pr[= seen | observed] * (digestInverse * (1 + cacheSize seen.2.2)) := by
          refine ENNReal.tsum_le_tsum fun seen => mul_le_mul' le_rfl ?_
          rw [bind_pure_comp, probEvent_map]
          exact probEvent_subtrees_ideal_le_size parameter seen.1 seen.2.1 seen.2.2
        _ = digestInverse * ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ∑' result, Pr[= result | idealRun adversary ⟨truncateHash output, parameter⟩] *
              (1 + cacheSize result.2) := by
          simp only [observed]
          simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          simp_rw [mul_left_comm _ digestInverse, ENNReal.tsum_mul_left]
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun output => mul_left_comm _ _ _
        _ ≤ _ := by
          refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl ?_)
          simp only [mul_add, mul_one, ENNReal.tsum_add, idealSize]
          exact add_le_add
            (tsum_probOutput_le_one (mx := idealRun adversary ⟨truncateHash output, parameter⟩))
            le_rfl

/-- On the executions without a request of the game's key generation, the forged top sibling is
the honest one with probability at most `(1 + N) / 2^128` on average over the public key. -/
theorem hiddenSibling_unsigned_le (adversary : Adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∧
            prefixResult.1.2 = [] |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] ≤
      digestInverse * publicKeyAverage fun publicKey => 1 + idealSize adversary publicKey := by
  have hdist : 𝒟[(simulateQ romImpl Concrete.scheme.keygen).run ∅] =
      𝒟[Concrete.materializeCachedKeyResult <$> (simulateQ romImpl Concrete.keygen).run ∅] := by
    rw [Concrete.evalDist_materialized_keygen_eq_precomputedKeygen]
    rfl
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun result : Forgery × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 |
            (simulateQ romImpl (forwardPhase adversary keyResult.1.1)).run keyResult.2] :=
      ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (probEvent_realRun_noSign_le keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2
          fun result => HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1)
    _ = ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
          Pr[fun result : Forgery × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 |
            (simulateQ romImpl (forwardPhase adversary keyResult.1.1)).run keyResult.2] := by
      rw [show (∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
          Pr[fun result : Forgery × QueryCache HashSpec =>
              HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 |
            (simulateQ romImpl (forwardPhase adversary keyResult.1.1)).run keyResult.2]) =
          ∑' keyResult, Pr[= keyResult | Concrete.materializeCachedKeyResult <$>
              (simulateQ romImpl Concrete.keygen).run ∅] *
            Pr[fun result : Forgery × QueryCache HashSpec =>
                HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 |
              (simulateQ romImpl (forwardPhase adversary keyResult.1.1)).run keyResult.2] from
        tsum_congr fun keyResult => by rw [probOutput_congr rfl hdist], tsum_probOutput_map_mul]
      rfl
    _ ≤ _ := hiddenSibling_forward_le adversary

end XmssSecurity.NoSign

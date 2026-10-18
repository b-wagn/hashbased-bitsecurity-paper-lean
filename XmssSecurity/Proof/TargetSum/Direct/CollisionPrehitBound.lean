import XmssSecurity.Proof.TargetSum.Direct.CollisionVerify
import XmssSecurity.Proof.Generic.Direct.DecidingSecondLane
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-!
# The prehit loss with 128-bit randomizers

A winning forgery with an encoding collision whose signed input was a prehit has probability at
most `collisionRate q` per expected direct encoding query, for an adversary making at most
`q < 2^127` direct encoding queries on every branch
(`winningEncodingPrehit_probability_le_collision`). The rate is at most
`(q + 2^85) / (2^128 (2^128 - 2^32))`, about `q/2^256`: a prehit only loses together with a
second collision.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct.Collision

variable {q : ℕ} {secretKey : Generic.SecretKey}

/-! ### The final verification -/

/-- The digests of the open prehits at an epoch. -/
def hitSet (secretKey : Generic.SecretKey) (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (leafIndex : LeafIndex) : Set Digest :=
  {digest | ∃ entry ∈ trace, entry.request.epoch = leafIndex ∧
    EntryOpen secretKey cache entry ∧ ∃ signature found, entry.signature = some signature ∧
      cache (input secretKey.parameter leafIndex (entry.request.message, signature.randomness)) =
        some found ∧ digest = Generic.truncateHash found}

theorem ncard_hitSet_le {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    (hnodup : trace.leafIndices.Nodup) (leafIndex : LeafIndex) :
    ((hitSet secretKey cache trace leafIndex).ncard : ℝ≥0∞) ≤
      (openCount secretKey cache trace : ℝ≥0∞) := by
  classical
  have hle1 : (hitSet secretKey cache trace leafIndex).ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    rintro a ⟨e1, he1, hep1, _, s1, f1, hs1, hf1, rfl⟩ b ⟨e2, he2, hep2, _, s2, f2, hs2, hf2, rfl⟩
    have heq : e1 = e2 := List.inj_on_of_nodup_map
      (by simpa [SigningCacheTrace.leafIndices] using hnodup) he1 he2 (hep1.trans hep2.symm)
    subst heq
    rw [hs1, Option.some.injEq] at hs2
    subst hs2
    rw [hf1, Option.some.injEq] at hf2
    rw [hf2]
  by_cases hempty : hitSet secretKey cache trace leafIndex = ∅
  · rw [hempty, Set.ncard_empty]
    simp
  · obtain ⟨digest, hdigest⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨entry, hentry, _, hopen, _⟩ := hdigest
    have hpos : 0 < openCount secretKey cache trace := by
      unfold openCount
      exact List.countP_pos_iff.mpr ⟨entry, hentry, by simpa using hopen⟩
    exact_mod_cast hle1.trans hpos

/-- A fresh query makes the state bad only if its digest is the digest of an open prehit. -/
theorem stateBad_cacheQuery {cache : QueryCache HashSpec} {trace : SigningCacheTrace}
    {remaining : ℕ} (hinv : Inv q secretKey cache trace remaining) {leafIndex : LeafIndex}
    {fresh : Message × Randomness}
    (hfresh : cache (input secretKey.parameter leafIndex fresh) = none) (output : HashOutput)
    (hbad : StateBad secretKey
      (cache.cacheQuery (input secretKey.parameter leafIndex fresh) output) trace) :
    StateBad secretKey cache trace ∨ Generic.truncateHash output ∈ hitSet secretKey cache trace leafIndex := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hnotBad, hnotHit⟩ := hcontra
  obtain ⟨entry, hentry, hprehit, signature, hsignature, hpartnered⟩ := hbad
  by_cases hepoch : entry.request.epoch = leafIndex
  · obtain ⟨found, hfound, _⟩ := hinv.valid entry hentry signature hsignature
    rw [hepoch] at hfound hpartnered
    rcases (isPartnered_cacheQuery_iff hfresh output hfound).mp hpartnered with hold | ⟨_, hsame⟩
    · exact hnotBad ⟨entry, hentry, hprehit, signature, hsignature, hepoch ▸ hold⟩
    · apply hnotHit
      refine ⟨entry, hentry, hepoch, ⟨hprehit, fun other hother hold => ?_⟩, signature, found,
        hsignature, hfound, hsame⟩
      rw [hsignature, Option.some.injEq] at hother
      subst hother
      exact hnotBad ⟨entry, hentry, hprehit, signature, hsignature, hold⟩
  · exact hnotBad ⟨entry, hentry, hprehit, signature, hsignature,
      (isPartnered_congr (fun x => agree_cacheQuery_other_leaf cache hepoch fresh output x) _).mp
        hpartnered⟩

/-- Verifying a forgery makes the state bad with probability at most the potential. -/
theorem verify_bad_le (publicKey : PublicKey) (hparameter : publicKey.parameter = secretKey.parameter)
    (forgery : Forgery) (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (remaining : ℕ)
    (hinv : Inv q secretKey cache trace remaining) :
    Pr[fun result : Bool × QueryCache HashSpec =>
        trace.leafIndices.Nodup ∧ StateBad secretKey result.2 trace |
      (simulateQ romImpl (Concrete.scheme.verify publicKey forgery.epoch forgery.message
        forgery.signature)).run cache] ≤ potential q secretKey cache trace remaining := by
  classical
  by_cases hnodup : trace.leafIndices.Nodup
  swap
  · refine le_trans (le_of_eq (probEvent_eq_zero fun result _ h => hnodup h.1)) bot_le
  by_cases hbad : StateBad secretKey cache trace
  · rw [potential_of_bad hnodup hbad]
    exact probEvent_le_one
  set forgedInput := input secretKey.parameter forgery.epoch
    (forgery.message, forgery.signature.randomness)
  have hrest : ∀ (startCache : QueryCache HashSpec) (output : HashOutput),
      ∀ result ∈ support ((simulateQ randomOracle (Direct.verifyAfterDigest publicKey forgery.epoch
        forgery.signature (Generic.truncateHash output))).run startCache),
        AgreeOnEncoding secretKey.parameter startCache result.2 := by
    intro startCache output result hresult
    rw [← hparameter]
    exact run_agree_of_noEncoding publicKey.parameter _
      (verifyAfterDigest_noEncoding _ _ _ _) startCache result hresult
  rw [Direct.simulateQ_romImpl_scheme_verify, StateT.run_bind]
  have hinput : Concrete.CacheView.encodingInput publicKey.parameter forgery.epoch
      (forgery.message, forgery.signature.randomness) = forgedInput := by
    rw [hparameter]
  rw [hinput]
  cases hcached : cache forgedInput with
  | some found =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hcached, pure_bind]
      refine le_trans (le_of_eq (probEvent_eq_zero fun result hresult h => hbad ?_)) bot_le
      exact (stateBad_congr (hrest cache found result hresult) trace).mp h.2
  | none =>
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, uniformHashOutput,
        bind_map_left, probEvent_bind_eq_tsum]
      have hstep : ∀ output : HashOutput,
          Pr[fun result : Bool × QueryCache HashSpec =>
              trace.leafIndices.Nodup ∧ StateBad secretKey result.2 trace |
            (simulateQ randomOracle (Direct.verifyAfterDigest publicKey forgery.epoch forgery.signature
              (Generic.truncateHash output))).run (cache.cacheQuery forgedInput output)] ≤
            if Generic.truncateHash output ∈ hitSet secretKey cache trace forgery.epoch then 1 else 0 := by
        intro output
        split_ifs with hhit
        · exact probEvent_le_one
        · refine le_of_eq (probEvent_eq_zero fun result hresult h => ?_)
          have hbadMid := (stateBad_congr (hrest _ output result hresult) trace).mp h.2
          rcases stateBad_cacheQuery hinv hcached output hbadMid with hold | hnew
          · exact hbad hold
          · exact hhit hnew
      calc
        _ ≤ ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
              (if Generic.truncateHash output ∈ hitSet secretKey cache trace forgery.epoch then 1 else 0) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (hstep output)
        _ = Pr[fun output : HashOutput =>
              Generic.truncateHash output ∈ hitSet secretKey cache trace forgery.epoch | $ᵗ HashOutput] := by
          rw [tsum_uniform_ite, mul_one, mul_zero, add_zero]
        _ = ((hitSet secretKey cache trace forgery.epoch).ncard : ℝ≥0∞) /
              ((2 ^ digestBits : ℕ) : ℝ≥0∞) := probEvent_truncate_mem _
        _ ≤ (openCount secretKey cache trace : ℝ≥0∞) * ENNReal.ofReal (1 / realN) := by
          have hN : 0 < realN := by unfold realN; positivity
          have h1N : ENNReal.ofReal (1 / realN) = 1 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
            rw [ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_one]
            simp [realN, digestBits]
            norm_num
          rw [h1N, ← mul_div_assoc, mul_one]
          exact ENNReal.div_le_div_right (ncard_hitSet_le hnodup _) _
        _ ≤ potential q secretKey cache trace remaining := by
          rw [potential_of_not_bad hnodup hbad]
          refine le_add_left (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
          apply div_le_div_of_nonneg_right _ (by unfold realN; positivity)
          have : (0 : ℝ) ≤ remaining := Nat.cast_nonneg _
          linarith

/-! ### The adversary's run -/

/-- The potential argument for any budget that bounds the remaining direct encoding queries
along every supported branch. -/
theorem collision_run_le_of_budget (hq : q + 1 ≤ 2 ^ 127) (publicKey : PublicKey) {α : Type}
    (terminal : α → QueryCache HashSpec → SigningCacheTrace → ℝ≥0∞)
    (hterminal : ∀ value cache trace remaining, Inv q secretKey cache trace remaining →
      terminal value cache trace ≤ potential q secretKey cache trace remaining)
    (Budget : OracleComp (OracleWorld + SigningSpec) α → ℕ →
      QueryCache HashSpec × SigningCacheTrace → Prop)
    (hBudget : ∀ input next remaining state, Budget (query input >>= next) remaining state →
      (Direct.IsDirectEncodingQuery secretKey.parameter input → 0 < remaining) ∧
      ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state),
        ∃ remaining' ≤ (if Direct.IsDirectEncodingQuery secretKey.parameter input then remaining - 1
          else remaining), Budget (next mid.1) remaining' mid.2) :
    ∀ (computation : OracleComp (OracleWorld + SigningSpec) α) (remaining : ℕ)
      (cache : QueryCache HashSpec) (trace : SigningCacheTrace),
        Budget computation remaining (cache, trace) →
        Inv q secretKey cache trace remaining →
        ∑' result, Pr[= result | (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey
            secretKey) computation).run (cache, trace)] *
            terminal result.1 result.2.1 result.2.2 ≤
          potential q secretKey cache trace remaining + collisionRate q *
            expectedSimulatedQueryCount (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
              (Direct.IsDirectEncodingQuery secretKey.parameter) computation (cache, trace) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro remaining cache trace _ hinv
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact (hterminal value cache trace remaining hinv).trans le_self_add
  | query_bind input next ih =>
      intro remaining cache trace hbudget hinv
      obtain ⟨hpos, hnext⟩ := hBudget input next remaining (cache, trace) hbudget
      rw [simulateQ_bind, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedSimulatedQueryCount_query_bind]
      simp only [simulateQ_spec_query]
      set impl := cappedCacheTracedMappedAdversaryImpl publicKey secretKey
      set predicate := Direct.IsDirectEncodingQuery secretKey.parameter
      set remaining' := if predicate input then remaining - 1 else remaining
      have hstep : (∑' mid, Pr[= mid | (impl input).run (cache, trace)] *
            potential q secretKey mid.2.1 mid.2.2 remaining') ≤
            potential q secretKey cache trace remaining +
              (if predicate input then collisionRate q else 0) ∧
          ∀ mid ∈ support ((impl input).run (cache, trace)),
            Inv q secretKey mid.2.1 mid.2.2 remaining' := by
        rcases input with (uniformInput | hashInput) | request
        · have hP : ¬ predicate (.inl (.inl uniformInput)) := by
            simp [predicate, Direct.IsDirectEncodingQuery]
          simp only [remaining', hP, if_false, add_zero]
          exact step_uniform publicKey uniformInput cache trace remaining hinv
        · by_cases henc : (encodingInputLeafIndex? secretKey.parameter hashInput).isSome
          · obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp henc
            obtain ⟨fresh, hfresh⟩ := exists_encodingInput_of_encodingInputLeafIndex?_eq_some
              secretKey.parameter hashInput leafIndex hleaf
            subst hfresh
            have hP : predicate (.inl (.inr (input secretKey.parameter leafIndex fresh))) := by
              simp [predicate, Direct.IsDirectEncodingQuery]
            have hrem : 0 < remaining := hpos hP
            obtain ⟨r, rfl⟩ : ∃ r, remaining = r + 1 := ⟨remaining - 1, by omega⟩
            simp only [remaining', hP, if_true, Nat.add_sub_cancel]
            exact step_hash_encoding hq publicKey leafIndex fresh cache trace r hinv
          · have hnone : encodingInputLeafIndex? secretKey.parameter hashInput = none :=
              Option.not_isSome_iff_eq_none.mp henc
            have hP : ¬ predicate (.inl (.inr hashInput)) := by
              simp [predicate, Direct.IsDirectEncodingQuery, hnone]
            simp only [remaining', hP, if_false, add_zero]
            exact step_hash_other publicKey hashInput hnone cache trace remaining hinv
        · have hP : ¬ predicate (.inr request) := by
            simp [predicate, Direct.IsDirectEncodingQuery]
          simp only [remaining', hP, if_false, add_zero]
          exact step_sign hq publicKey request cache trace remaining hinv
      obtain ⟨hpotential, hinvStep⟩ := hstep
      calc
        _ ≤ ∑' mid, Pr[= mid | (impl input).run (cache, trace)] *
              (potential q secretKey mid.2.1 mid.2.2 remaining' + collisionRate q *
                expectedSimulatedQueryCount impl predicate (next mid.1) mid.2) := by
          refine ENNReal.tsum_le_tsum fun mid => ?_
          by_cases hmid : mid ∈ support ((impl input).run (cache, trace))
          · obtain ⟨n', hn', hb⟩ := hnext mid hmid
            exact mul_le_mul' le_rfl ((ih mid.1 n' mid.2.1 mid.2.2 hb
              ((hinvStep mid hmid).mono_remaining hn')).trans
                (add_le_add (potential_remaining_mono hn') le_rfl))
          · rw [probOutput_eq_zero_of_not_mem_support hmid, zero_mul, zero_mul]
        _ = (∑' mid, Pr[= mid | (impl input).run (cache, trace)] *
              potential q secretKey mid.2.1 mid.2.2 remaining') +
            collisionRate q * ∑' mid, Pr[= mid | (impl input).run (cache, trace)] *
              expectedSimulatedQueryCount impl predicate (next mid.1) mid.2 := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun mid => ?_
          ring
        _ ≤ (potential q secretKey cache trace remaining +
              (if predicate input then collisionRate q else 0)) +
            collisionRate q * ∑' mid, Pr[= mid | (impl input).run (cache, trace)] *
              expectedSimulatedQueryCount impl predicate (next mid.1) mid.2 :=
          add_le_add hpotential le_rfl
        _ = _ := by
          split_ifs <;> ring

/-! ### The game -/

theorem leafPotential_of_empty {parameter : PublicParameter} {cache : QueryCache HashSpec}
    {leafIndex : LeafIndex} (h : ∀ entry, cache (input parameter leafIndex entry) = none) :
    leafPotential q parameter cache leafIndex = 0 := by
  classical
  have hentries : entries parameter cache leafIndex = ∅ := by
    ext entry
    simp [mem_entries, h entry]
  have hvalid : validEntries parameter cache leafIndex = ∅ :=
    Set.subset_eq_empty validEntries_subset_entries hentries
  have hpartnered : partneredEntries parameter cache leafIndex = ∅ :=
    Set.subset_eq_empty partneredEntries_subset_valid hvalid
  have hcached : ∀ message, cachedRandomizersAt parameter leafIndex message cache = ∅ := by
    intro message
    ext randomness
    simp [cachedRandomizersAt, show Concrete.CacheView.encodingInput parameter leafIndex
      (message, randomness) = input parameter leafIndex (message, randomness) from rfl,
      h (message, randomness)]
  have hvalidR : ∀ message, validRandomizers parameter cache leafIndex message = ∅ := by
    intro message
    exact Finset.subset_empty.mp (hcached message ▸ validRandomizers_subset_cached message)
  unfold leafPotential
  simp only [hentries, hvalid, hpartnered, hcached, hvalidR, Set.ncard_empty, Finset.card_empty,
    Nat.cast_zero, CollisionMath.leafMain, CollisionMath.msgTerm]
  simp

/-- After key generation: the adversary's run and the verification. -/
theorem collision_afterKeygen_le (adversary : Adversary) (hq : q + 1 ≤ 2 ^ 127)
    (publicKey : PublicKey) (secretKey : Generic.SecretKey) (keyCache : QueryCache HashSpec)
    (hparameter : publicKey.parameter = secretKey.parameter)
    (hempty : ∀ leafIndex entry, keyCache (input secretKey.parameter leafIndex entry) = none)
    (Budget : OracleComp (OracleWorld + SigningSpec) Forgery → ℕ →
      QueryCache HashSpec × SigningCacheTrace → Prop)
    (hBudget : ∀ input next remaining state, Budget (query input >>= next) remaining state →
      (Direct.IsDirectEncodingQuery secretKey.parameter input → 0 < remaining) ∧
      ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run state),
        ∃ remaining' ≤ (if Direct.IsDirectEncodingQuery secretKey.parameter input then remaining - 1
          else remaining), Budget (next mid.1) remaining' mid.2)
    (hstart : Budget (adversary.main publicKey) q (keyCache, [])) :
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          ∃ entry ∈ execution.2.2, entry.EncodingInputPrehit execution.1.secretKey ∧
            entry.PrehitPartnered execution.1.secretKey execution.2.1 |
      cappedDetailedGameAfterKeygenWithSigningTrace adversary publicKey secretKey keyCache] ≤
      collisionRate q * expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl publicKey secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) keyCache := by
  classical
  have hnil : (SigningCacheTrace.leafIndices []).Nodup := by
    simp [SigningCacheTrace.leafIndices]
  have hinv : Inv q secretKey keyCache [] q := by
    refine ⟨?_, fun entry hentry => absurd hentry (List.not_mem_nil)⟩
    have hzero : unsignedCount secretKey keyCache [] = 0 := by
      unfold unsignedCount
      refine Finset.sum_eq_zero fun leafIndex _ => ?_
      have : entries secretKey.parameter keyCache leafIndex = ∅ := by
        ext entry
        simp [mem_entries, hempty leafIndex entry]
      simp [this]
    rw [hzero, zero_add]
  have hpotential : potential q secretKey keyCache [] q = 0 := by
    have hnotBad : ¬ StateBad secretKey keyCache [] := fun ⟨_, h, _⟩ => List.not_mem_nil h
    rw [potential_of_not_bad hnil hnotBad]
    have hsum : unsignedSum q secretKey keyCache [] = 0 := by
      unfold unsignedSum
      refine Finset.sum_eq_zero fun leafIndex _ => ?_
      simp only [SigningCacheTrace.leafIndices, List.map_nil, List.not_mem_nil, if_false]
      exact leafPotential_of_empty (hempty leafIndex)
    simp [hsum, openCount]
  have hterm : ∀ (forgery : Forgery) (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
      (remaining : ℕ), Inv q secretKey cache trace remaining →
      Pr[fun verification : Bool × QueryCache HashSpec =>
          trace.leafIndices.Nodup ∧ StateBad secretKey verification.2 trace |
        (simulateQ romImpl (Concrete.scheme.verify publicKey forgery.epoch forgery.message
          forgery.signature)).run cache] ≤ potential q secretKey cache trace remaining :=
    fun forgery cache trace remaining hinvState =>
      verify_bad_le publicKey hparameter forgery cache trace remaining hinvState
  unfold cappedDetailedGameAfterKeygenWithSigningTrace
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey
          secretKey) (adversary.main publicKey)).run (keyCache, [])] *
          Pr[fun verification : Bool × QueryCache HashSpec =>
              result.2.2.leafIndices.Nodup ∧ StateBad secretKey verification.2 result.2.2 |
            (simulateQ romImpl (Concrete.scheme.verify publicKey result.1.epoch result.1.message
              result.1.signature)).run result.2.1] := by
      refine ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl ?_
      rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine ENNReal.tsum_le_tsum fun verification => ?_
      obtain ⟨verified, finalCache⟩ := verification
      by_cases hgood : result.2.2.leafIndices.Nodup ∧ StateBad secretKey finalCache result.2.2
      · rw [if_pos hgood]
        exact mul_le_of_le_one_right' probEvent_le_one
      rw [if_neg hgood]
      refine le_of_eq (mul_eq_zero.mpr (Or.inr ?_))
      simp only [probEvent_pure]
      rw [if_neg]
      intro hevent
      apply hgood
      obtain ⟨hencoding, entry, hentry, hprehit, signature, out, hsignature, hout, hvalid,
        other, hother, otherOut, hotherCache, hsame⟩ := hevent
      refine ⟨?_, entry, hentry, hprehit, signature, hsignature,
        out, hout, hvalid, other, hother, otherOut, hotherCache, hsame⟩
      have hvalidLog := hencoding.signingTranscript_valid
      unfold SigningTranscript.Valid at hvalidLog
      simpa [SigningCacheTrace.leafIndices, SigningCacheTrace.toSigningLog,
        List.map_map, Function.comp_def] using hvalidLog
    _ ≤ potential q secretKey keyCache [] q + collisionRate q *
          expectedSimulatedQueryCount (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
            (Direct.IsDirectEncodingQuery secretKey.parameter) (adversary.main publicKey) (keyCache, []) :=
      collision_run_le_of_budget (α := Forgery) hq publicKey
        (fun (forgery : Forgery) (cache : QueryCache HashSpec) (trace : SigningCacheTrace) =>
          Pr[fun verification : Bool × QueryCache HashSpec =>
            trace.leafIndices.Nodup ∧ StateBad secretKey verification.2 trace |
          (simulateQ romImpl (Concrete.scheme.verify publicKey forgery.epoch forgery.message
            forgery.signature)).run cache])
        hterm Budget hBudget (adversary.main publicKey) q keyCache [] hstart hinv
    _ = _ := by
      rw [hpotential, zero_add, cappedCacheTracedMappedAdversaryImpl,
        Direct.expectedSimulatedQueryCount_extendState]

/-- The prehit loss of a forgery is at most `collisionRate q` per expected direct encoding query,
for any budget that bounds the adversary's direct encoding queries by `q < 2^127` along every
supported branch. -/
theorem winningEncodingPrehit_probability_le_collision_of_budget (adversary : Adversary) (q : ℕ)
    (hq : q + 1 ≤ 2 ^ 127)
    (Budget : PublicKey → Generic.SecretKey → OracleComp (OracleWorld + SigningSpec) Forgery → ℕ →
      QueryCache HashSpec × SigningCacheTrace → Prop)
    (hBudget : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ input next remaining state,
        Budget keyResult.1.1 keyResult.1.2 (query input >>= next) remaining state →
        (Direct.IsDirectEncodingQuery keyResult.1.2.parameter input → 0 < remaining) ∧
        ∀ mid ∈ support ((cappedCacheTracedMappedAdversaryImpl keyResult.1.1 keyResult.1.2
            input).run state),
          ∃ remaining' ≤ (if Direct.IsDirectEncodingQuery keyResult.1.2.parameter input then remaining - 1
            else remaining), Budget keyResult.1.1 keyResult.1.2 (next mid.1) remaining' mid.2)
    (hstart : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      Budget keyResult.1.1 keyResult.1.2 (adversary.main keyResult.1.1) q (keyResult.2, [])) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      collisionRate q * Direct.expectedDirectEncodingQueries adversary := by
  calc
    _ ≤ Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
          WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
            ∃ entry ∈ execution.2.2, entry.EncodingInputPrehit execution.1.secretKey ∧
              entry.PrehitPartnered execution.1.secretKey execution.2.1 |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      exact probEvent_mono fun execution _ h => h
    _ ≤ _ := by
      unfold cappedDetailedGameWithSigningTrace Direct.expectedDirectEncodingQueries
      rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun keyResult => ?_
      rw [← mul_assoc, mul_comm (collisionRate q), mul_assoc]
      by_cases hkeyResult : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      swap
      · rw [probOutput_eq_zero_of_not_mem_support hkeyResult, zero_mul, zero_mul]
      refine mul_le_mul' le_rfl ?_
      have hparameter : keyResult.1.1.parameter = keyResult.1.2.parameter :=
        Deciding.keygen_publicKey_parameter_eq keyResult hkeyResult
      have hmem : keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
        simpa only [Concrete.scheme] using hkeyResult
      have hempty : ∀ leafIndex entry,
          keyResult.2 (input keyResult.1.2.parameter leafIndex entry) = none :=
        fun leafIndex entry =>
          Concrete.precomputedKeygen_cache_none_encodingInput keyResult hmem leafIndex entry
      exact collision_afterKeygen_le adversary hq keyResult.1.1 keyResult.1.2 keyResult.2
        hparameter hempty (Budget keyResult.1.1 keyResult.1.2) (hBudget keyResult hkeyResult)
        (hstart keyResult hkeyResult)

/-- The prehit loss for an adversary making at most `q < 2^127` direct encoding queries. -/
theorem winningEncodingPrehit_probability_le_collision (adversary : Adversary) (q : ℕ)
    (hq : q + 1 ≤ 2 ^ 127) (hbound : Direct.IsEncodingQueryBound adversary q) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      collisionRate q * Direct.expectedDirectEncodingQueries adversary :=
  winningEncodingPrehit_probability_le_collision_of_budget adversary q hq
    (fun _ secretKey computation remaining _ =>
      computation.IsQueryBoundP (Direct.IsDirectEncodingQuery secretKey.parameter) remaining)
    (fun _ _ input next remaining _ hbound => by
      change (liftM (OracleSpec.query input) >>= next).IsQueryBoundP _ _ at hbound
      rw [isQueryBoundP_query_bind_iff] at hbound
      exact ⟨fun hP => hbound.1.resolve_left (not_not.mpr hP),
        fun mid _ => ⟨_, le_rfl, hbound.2 mid.1⟩⟩)
    (fun keyResult hkeyResult => by
      have hparameter : keyResult.1.1.parameter = keyResult.1.2.parameter :=
        Deciding.keygen_publicKey_parameter_eq keyResult hkeyResult
      rw [← hparameter]
      exact hbound keyResult.1.1)

end XmssSecurity.TargetSum.Direct.Collision

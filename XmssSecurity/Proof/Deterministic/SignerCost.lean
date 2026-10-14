import XmssSecurity.Proof.Deterministic.TableSigner
import XmssSecurity.Proof.SignerEncodingCost

/-! Presampling randomizers preserves the full cost of signing when each table attempt
is charged twice. The joint distribution includes the answer, cost, and final hash cache. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity

theorem countHashQueries_precomputedSignAttempt
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    countHashQueries (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp OracleWorld (Option Signature)) =
      (fun answer => (answer, 1)) <$>
        (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp OracleWorld (Option Signature)) := by
  have hencoding : countHashQueries
      (Concrete.encodingHash secretKey.parameter leafIndex message randomness :
        OracleComp OracleWorld Digest) =
      (fun digest => (digest, 1)) <$>
        (Concrete.encodingHash secretKey.parameter leafIndex message randomness :
          OracleComp OracleWorld Digest) := by
    change countHashQueries (liftM (OracleWorld.query (.inr
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, randomness))))
      >>= fun output => pure (truncateHash output)) = _
    rw [countHashQueries_query_bind]
    simp only [countHashQueries_pure, pure_bind]
    rfl
  rw [Concrete.precomputedSignAttempt, countHashQueries_bind, hencoding]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro digest
  cases TargetSum.decodeDigest digest <;>
    simp only [countHashQueries_pure, pure_bind, map_pure, Nat.add_zero]

namespace Seeded

theorem run_counted_deriveRandomizer_of_cached
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) (cache : QueryCache HashSpec)
    (output : HashOutput)
    (hcache : cache (randomizerHashInput parameter seed leafIndex message trial) = some output) :
    (simulateQ romImpl (countHashQueries
      (deriveRandomizer parameter seed leafIndex message trial :
        OracleComp OracleWorld Randomness))).run cache =
      pure ((output.extractLsb' 0 randomnessBits, 1), cache) := by
  unfold deriveRandomizer Concrete.oracleHash
  change (simulateQ romImpl (countHashQueries
    (liftM (OracleWorld.query (.inr (randomizerHashInput parameter seed leafIndex message trial)))
      >>= fun value => pure (value.extractLsb' 0 randomnessBits)))).run cache = _
  rw [countHashQueries_query_bind]
  simp only [countHashQueries_pure, pure_bind, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do
    let result ← (randomOracle (spec := HashSpec)
      (randomizerHashInput parameter seed leafIndex message trial)).run cache
    pure ((result.1.extractLsb' 0 randomnessBits, 1), result.2)) = _
  rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]

theorem tableSignFrom_lift_hash_eq_world
    (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    (liftM (tableSignFrom randomizers secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) =
      tableSignFrom randomizers secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [tableSignFrom]
  | succ attempts ih =>
      simp only [tableSignFrom, liftM_bind, Concrete.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

theorem evalDist_counted_signFrom_eq_twice_tableSignFrom
    (seed : MasterSeed) (secretKey : XmssSecurity.SecretKey)
    (randomizers : RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (attempts trial : Nat) (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ romImpl (countHashQueries
      (signFrom ⟨seed, secretKey⟩ leafIndex message attempts trial :
        OracleComp OracleWorld (Option Signature)))).run cache] =
      𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
        (simulateQ romImpl (countHashQueries
          (tableSignFrom randomizers secretKey leafIndex message attempts trial :
            OracleComp OracleWorld (Option Signature)))).run cache] := by
  induction attempts generalizing trial cache with
  | zero => simp [signFrom, tableSignFrom, countHashQueries_pure]
  | succ attempts ih =>
      rw [signFrom, countHashQueries_bind]
      simp only [simulateQ_bind, StateT.run_bind]
      rw [run_counted_deriveRandomizer_of_cached _ _ _ _ _ _ _
        (hcache (⟨leafIndex, message⟩, BitVec.ofNat 32 trial)), pure_bind]
      rw [tableSignFrom, countHashQueries_bind]
      simp only [countHashQueries_bind, countHashQueries_precomputedSignAttempt,
        simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, bind_map_left, map_bind, pure_bind, map_pure, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      have hnext : ∀ position, result.2 (randomizerInputs secretKey.parameter seed position) =
          some (randomizers position) := fun position =>
        (xmssRom_cache_le _ cache result hresult) (hcache position)
      cases result.1 with
      | some signature => simp [countHashQueries_pure]
      | none =>
          have h := ih (trial + 1) result.2 hnext
          have hm := congrArg (fun distribution =>
            (fun value => ((value.1.1, 2 + value.1.2), value.2)) <$> distribution) h
          simpa only [bind_pure_comp, evalDist_map, Functor.map_map, Nat.mul_add, Nat.mul_one,
            ← Nat.add_assoc] using hm

theorem evalDist_counted_sign_eq_twice_tableSign
    (seed : MasterSeed) (secretKey : XmssSecurity.SecretKey)
    (randomizers : RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ romImpl (countHashQueries
      (scheme.sign ⟨seed, secretKey⟩ leafIndex message))).run cache] =
      𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
        (simulateQ romImpl (countHashQueries
          ((tableScheme randomizers).sign secretKey leafIndex message))).run cache] := by
  change 𝒟[(simulateQ romImpl (countHashQueries
      (liftM (signFrom ⟨seed, secretKey⟩ leafIndex message signingAttemptLimit 0 :
        OracleComp HashSpec (Option Signature))))).run cache] =
    𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
      (simulateQ romImpl (countHashQueries
        (liftM (tableSignFrom randomizers secretKey leafIndex message signingAttemptLimit 0 :
          OracleComp HashSpec (Option Signature))))).run cache]
  rw [signFrom_lift_hash_eq_world, tableSignFrom_lift_hash_eq_world]
  exact evalDist_counted_signFrom_eq_twice_tableSignFrom _ _ _ _ _ _ _ _ hcache

/-- The reference attempt count consumes two units of the original signer budget. -/
theorem twice_tableSign_count_le_of_sign_hashQueryBound
    (seed : MasterSeed) (secretKey : XmssSecurity.SecretKey)
    (randomizers : RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) (q : Nat)
    (hbound : HashQueryBound (scheme.sign ⟨seed, secretKey⟩ leafIndex message) cache q)
    (result : (Option Signature × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries
      ((tableScheme randomizers).sign secretKey leafIndex message))).run cache)) :
    2 * result.1.2 ≤ q := by
  apply (hashQueryBound_iff_run _ _ _).1 hbound ((result.1.1, 2 * result.1.2), result.2)
  rw [mem_support_iff_of_evalDist_eq
    (evalDist_counted_sign_eq_twice_tableSign _ _ _ _ _ _ hcache), support_map]
  exact ⟨result, hresult, rfl⟩

/-- info: 'XmssSecurity.Seeded.evalDist_counted_sign_eq_twice_tableSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_counted_sign_eq_twice_tableSign

/-- info: 'XmssSecurity.Seeded.twice_tableSign_count_le_of_sign_hashQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twice_tableSign_count_le_of_sign_hashQueryBound

end Seeded
end XmssSecurity

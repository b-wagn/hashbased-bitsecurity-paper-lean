import XmssSecurity.Proof.Generic.Deterministic.TableSigner
import XmssSecurity.Proof.TargetSum.SignerEncodingCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Presampling randomizers preserves the full cost of signing when each table attempt
is charged twice. The joint distribution includes the answer, cost, and final hash cache. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum

theorem countHashQueries_precomputedSignAttempt
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) :
    countHashQueries (Generic.Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp OracleWorld (Option Generic.Signature)) =
      (fun answer => (answer, 1)) <$>
        (Generic.Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
          OracleComp OracleWorld (Option Generic.Signature)) := by
  have hencoding : countHashQueries
      (Generic.Concrete.encodingHash secretKey.parameter leafIndex message randomness :
        OracleComp OracleWorld Digest) =
      (fun digest => (digest, 1)) <$>
        (Generic.Concrete.encodingHash secretKey.parameter leafIndex message randomness :
          OracleComp OracleWorld Digest) := by
    change countHashQueries (liftM (OracleWorld.query (.inr
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, randomness))))
      >>= fun output => pure (Generic.truncateHash output)) = _
    rw [countHashQueries_query_bind]
    simp only [countHashQueries_pure, pure_bind]
    rfl
  rw [Generic.Concrete.precomputedSignAttempt, countHashQueries_bind, hencoding]
  simp only [bind_map_left, map_bind]
  apply bind_congr
  intro digest
  cases Code.decodeDigest digest <;>
    simp only [countHashQueries_pure, pure_bind, map_pure, Nat.add_zero]

namespace Seeded

theorem run_counted_deriveRandomizer_of_cached
    (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) (cache : QueryCache HashSpec)
    (output : HashOutput)
    (hcache : cache (Generic.randomizerHashInput parameter seed leafIndex message trial) = some output) :
    (simulateQ romImpl (countHashQueries
      (Generic.deriveRandomizer parameter seed leafIndex message trial :
        OracleComp OracleWorld Randomness))).run cache =
      pure ((output.extractLsb' 0 randomnessBits, 1), cache) := by
  unfold Generic.deriveRandomizer Generic.Concrete.oracleHash
  change (simulateQ romImpl (countHashQueries
    (liftM (OracleWorld.query (.inr (Generic.randomizerHashInput parameter seed leafIndex message trial)))
      >>= fun value => pure (value.extractLsb' 0 randomnessBits)))).run cache = _
  rw [countHashQueries_query_bind]
  simp only [countHashQueries_pure, pure_bind, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do
    let result ← (randomOracle (spec := HashSpec)
      (Generic.randomizerHashInput parameter seed leafIndex message trial)).run cache
    pure ((result.1.extractLsb' 0 randomnessBits, 1), result.2)) = _
  rw [QueryImpl.withCaching_run_some _ hcache, pure_bind]

theorem tableSignFrom_lift_hash_eq_world
    (randomizers : Seeded.RandomizerOutputs) (secretKey : Generic.SecretKey)
    (leafIndex : LeafIndex) (message : Message) (attempts trial : Nat) :
    (liftM (Seeded.tableSignFrom randomizers secretKey leafIndex message attempts trial :
      OracleComp HashSpec (Option Generic.Signature)) : OracleComp OracleWorld (Option Generic.Signature)) =
      Seeded.tableSignFrom randomizers secretKey leafIndex message attempts trial := by
  induction attempts generalizing trial with
  | zero => simp [Seeded.tableSignFrom]
  | succ attempts ih =>
      simp only [Seeded.tableSignFrom, liftM_bind, Concrete.precomputedSignAttempt_lift_hash_eq_world]
      apply bind_congr
      intro answer
      cases answer <;> simp only [ih, liftM_pure]

theorem evalDist_counted_signFrom_eq_twice_tableSignFrom
    (seed : MasterSeed) (secretKey : Generic.SecretKey)
    (randomizers : Seeded.RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (attempts trial : Nat) (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (Seeded.randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ romImpl (countHashQueries
      (Generic.Seeded.signFrom ⟨seed, secretKey⟩ leafIndex message attempts trial :
        OracleComp OracleWorld (Option Generic.Signature)))).run cache] =
      𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
        (simulateQ romImpl (countHashQueries
          (Seeded.tableSignFrom randomizers secretKey leafIndex message attempts trial :
            OracleComp OracleWorld (Option Generic.Signature)))).run cache] := by
  induction attempts generalizing trial cache with
  | zero => simp [Generic.Seeded.signFrom, Seeded.tableSignFrom, countHashQueries_pure]
  | succ attempts ih =>
      rw [Generic.Seeded.signFrom, countHashQueries_bind]
      simp only [simulateQ_bind, StateT.run_bind]
      rw [run_counted_deriveRandomizer_of_cached _ _ _ _ _ _ _
        (hcache (⟨leafIndex, message⟩, BitVec.ofNat 32 trial)), pure_bind]
      rw [Seeded.tableSignFrom, countHashQueries_bind]
      simp only [countHashQueries_bind, countHashQueries_precomputedSignAttempt,
        simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, bind_map_left, map_bind, pure_bind, map_pure, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      have hnext : ∀ position, result.2 (Seeded.randomizerInputs secretKey.parameter seed position) =
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
    (seed : MasterSeed) (secretKey : Generic.SecretKey)
    (randomizers : Seeded.RandomizerOutputs) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : ∀ position, cache (Seeded.randomizerInputs secretKey.parameter seed position) =
      some (randomizers position)) :
    𝒟[(simulateQ romImpl (countHashQueries
      (Seeded.scheme.sign ⟨seed, secretKey⟩ leafIndex message))).run cache] =
      𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
        (simulateQ romImpl (countHashQueries
          ((Seeded.tableScheme randomizers).sign secretKey leafIndex message))).run cache] := by
  change 𝒟[(simulateQ romImpl (countHashQueries
      (liftM (Generic.Seeded.signFrom ⟨seed, secretKey⟩ leafIndex message signingAttemptLimit 0 :
        OracleComp HashSpec (Option Generic.Signature))))).run cache] =
    𝒟[(fun result => ((result.1.1, 2 * result.1.2), result.2)) <$>
      (simulateQ romImpl (countHashQueries
        (liftM (Seeded.tableSignFrom randomizers secretKey leafIndex message signingAttemptLimit 0 :
          OracleComp HashSpec (Option Generic.Signature))))).run cache]
  rw [signFrom_lift_hash_eq_world, tableSignFrom_lift_hash_eq_world]
  exact evalDist_counted_signFrom_eq_twice_tableSignFrom _ _ _ _ _ _ _ _ hcache

/-- info: 'XmssSecurity.TargetSum.Seeded.evalDist_counted_sign_eq_twice_tableSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalDist_counted_sign_eq_twice_tableSign

end Seeded
end XmssSecurity.TargetSum

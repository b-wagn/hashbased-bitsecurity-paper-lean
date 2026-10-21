import SlhDsaSecurity.Proof.KeygenFresh

/-! Distribution of the actual public key under the initially empty shared oracle. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.KeygenUniform

def splitOutput (output : HashOutput) : Digest × BitVec 112 :=
  (Hashing.truncate output, output.extractLsb' 0 112)

theorem splitOutput_bijective : Function.Bijective splitOutput := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro left right h
    have hleft : Hashing.truncate left ++ left.extractLsb' 0 112 = left :=
      BitVec.extractLsb'_append_extractLsb'
    have hright : Hashing.truncate right ++ right.extractLsb' 0 112 = right :=
      BitVec.extractLsb'_append_extractLsb'
    rw [← hleft, ← hright]
    exact congrArg₂ HAppend.hAppend (congrArg Prod.fst h) (congrArg Prod.snd h)
  · norm_num [HashOutput, Digest, messageDigestBytes, n, Fintype.card_prod, card_bitVec]

theorem truncate_uniform :
    𝒟[Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hmap : Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (splitOutput <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, splitOutput]
  have hsplit := evalDist_map_bijective_uniform_cross (α := HashOutput)
    (β := Digest × BitVec 112) splitOutput splitOutput_bijective
  rw [hmap, evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

theorem fresh_tweakable_uniform (seed : Digest) (address : Address) (payload : Bytes)
    (cache : QueryCache HashSpec) (hfresh : cache (Hashing.tweakableInput seed address payload) = none) :
    𝒟[(simulateQ rom
      (Hashing.tweakable seed address payload : OracleComp OracleWorld Digest)).run' cache] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hrun : (simulateQ rom
      (Hashing.tweakable seed address payload : OracleComp OracleWorld Digest)).run' cache =
      Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
    unfold Hashing.tweakable Hashing.shortHash Hashing.hash
    simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_pure]
    rw [show simulateQ rom (query (spec := HashSpec)
        (m := OracleComp OracleWorld) (Hashing.tweakableInput seed address payload)) =
      randomOracle (Hashing.tweakableInput seed address payload) from
        roSim.simulateQ_HasQuery_query randomOracle _]
    change Prod.fst <$> ((randomOracle (Hashing.tweakableInput seed address payload)).run cache >>=
      fun result => pure (Hashing.truncate result.1, result.2)) = _
    rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
    simp [uniformSampleImpl, Functor.map_map]
  rw [hrun]
  exact truncate_uniform

/-- A computation with the same conditional output law at every supported result has that law. -/
theorem evalDist_bind_eq_of_support {α β : Type} (computation : ProbComp α)
    (next : α → ProbComp β) (target : ProbComp β)
    (hnext : ∀ result ∈ support computation, 𝒟[next result] = 𝒟[target]) :
    𝒟[computation >>= next] = 𝒟[target] := by
  apply evalDist_ext
  intro output
  rw [probOutput_bind_eq_tsum]
  have hmass : ∑' result, Pr[= result | computation] = 1 :=
    tsum_probOutput_eq_one' (by simp)
  calc
    _ = ∑' result, Pr[= result | computation] * Pr[= output | target] := by
      apply tsum_congr
      intro result
      by_cases hresult : result ∈ support computation
      · simp only [probOutput_def]
        rw [hnext result hresult]
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, hmass, one_mul]

theorem top_root_uniform (secretSeed seed : Digest) :
    𝒟[(simulateQ rom (Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0)
      subtreeHeight 0 : OracleComp OracleWorld Digest)).run' ∅] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hnode : (Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0)
      subtreeHeight 0 : OracleComp OracleWorld Digest) = (do
        let children ← topChildren secretSeed seed
        Hashing.tweakable seed rootAddress
          (bytesBE n children.1 ++ bytesBE n children.2)) := by
    change (Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0)
      (8 + 1) 0 : OracleComp OracleWorld Digest) = _
    rw [Merkle.node]
    simp [topChildren, rootAddress, subtreeHeight, bind_assoc]
  rw [hnode, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply evalDist_bind_eq_of_support
  intro result hresult
  exact fresh_tweakable_uniform seed rootAddress _ result.2
    (topChildren_root_fresh secretSeed seed result hresult _)

def publicPair (keys : SecretKey × PublicKey) : Digest × Digest :=
  (keys.2.seed, keys.2.root)

theorem keygenInternal_publicPair_uniform (secretSeed prfSeed seed : Digest) :
    𝒟[publicPair <$> XmssSecurity.RandomOracleModel.run
      (Scheme.keygenInternal secretSeed prfSeed seed :
        OracleComp OracleWorld (SecretKey × PublicKey))] =
      𝒟[(fun root => (seed, root)) <$> ($ᵗ Digest : ProbComp Digest)] := by
  have hmap : publicPair <$> XmssSecurity.RandomOracleModel.run
      (Scheme.keygenInternal secretSeed prfSeed seed :
        OracleComp OracleWorld (SecretKey × PublicKey)) =
      (fun root => (seed, root)) <$>
        (simulateQ rom (Merkle.node secretSeed seed (Hypertree.address (layers - 1) 0)
          subtreeHeight 0 : OracleComp OracleWorld Digest)).run' ∅ := by
    simp [XmssSecurity.RandomOracleModel.run, Scheme.keygenInternal, publicPair,
      StateT.run'_eq, Functor.map_map, rom]
  rw [hmap, evalDist_map, top_root_uniform, ← evalDist_map]

theorem keygen_run :
    XmssSecurity.RandomOracleModel.run
      (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey)) = (do
        let secretSeed ← $ᵗ Digest
        let prfSeed ← $ᵗ Digest
        let seed ← $ᵗ Digest
        XmssSecurity.RandomOracleModel.run
          (Scheme.keygenInternal secretSeed prfSeed seed :
            OracleComp OracleWorld (SecretKey × PublicKey))) := by
  have hsample : (simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest) :
      OracleComp OracleWorld Digest) = liftM ($ᵗ Digest : ProbComp Digest) := rfl
  unfold XmssSecurity.RandomOracleModel.run Scheme.keygen
  simp_rw [hsample, simulateQ_bind]
  unfold XmssSecurity.RandomOracleModel.impl
  rw [roSim.run'_liftM_bind]
  apply bind_congr
  intro secretSeed
  rw [roSim.run'_liftM_bind]
  apply bind_congr
  intro prfSeed
  rw [roSim.run'_liftM_bind]

attribute [local irreducible] Scheme.keygenInternal

/-- Public seed and public root are independent uniform 16-byte strings in the actual keygen. -/
theorem publicPair_uniform :
    𝒟[publicPair <$> XmssSecurity.RandomOracleModel.run
      (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey))] =
      𝒟[($ᵗ (Digest × Digest) : ProbComp (Digest × Digest))] := by
  rw [keygen_run]
  simp only [map_bind]
  apply evalDist_bind_eq_of_support
  intro secretSeed _
  apply evalDist_bind_eq_of_support
  intro prfSeed _
  have hinner : 𝒟[(do
      let seed ← $ᵗ Digest
      publicPair <$> XmssSecurity.RandomOracleModel.run
        (Scheme.keygenInternal secretSeed prfSeed seed :
          OracleComp OracleWorld (SecretKey × PublicKey)))] =
      𝒟[(do
        let seed ← $ᵗ Digest
        (fun root => (seed, root)) <$> ($ᵗ Digest : ProbComp Digest))] := by
    rw [evalDist_bind, evalDist_bind]
    exact congrArg _ (funext fun seed => keygenInternal_publicPair_uniform secretSeed prfSeed seed)
  rw [hinner]
  rfl

/-- The byte-format overlap bound now applies to actual key generation, with no key-law premise. -/
theorem keygen_prob_possible_le :
    Pr[fun keys => HashSeparation.Possible (publicPair keys) |
      XmssSecurity.RandomOracleModel.run
        (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey))] ≤
      1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  rw [show (fun keys => HashSeparation.Possible (publicPair keys)) =
    HashSeparation.Possible ∘ publicPair from rfl, ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) publicPair_uniform]
  exact HashSeparation.prob_possible_le

end SlhDsaSecurity.KeygenUniform

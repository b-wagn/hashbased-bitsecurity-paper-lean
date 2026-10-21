import SlhDsaSecurity.Proof.KeygenUniform
import SlhDsaSecurity.Proof.MessageDigest

/-!
# A fresh message digest is uniform in the actual shared oracle

Every FORS bound in this development — coverage, the occupancy and Poisson concentration
results, the adaptive-target and leave-one-out charges — is proved about *independent
tapes* of uniform digest views. Transferring them to the experiment needs the real-oracle
counterpart of that assumption, which is what this file supplies.

`MessageDigest.evalDist_parse_uniform` says the standard 21/7/2-byte parser sends a uniform
thirty-byte answer to a uniform `View` (a 63-bit FORS instance together with fourteen
12-bit leaf indices), retaining the nine ignored bits so the map is a bijection.
`fresh_messageDigest_parse_uniform` composes that with the exact law of an uncached call to
the shared oracle: when the specified `H_msg` byte input is absent from the cache, the
actual call answers uniformly on all 240 bits, so its parsed view is uniform.

This is the freshness half of the FORS coupling, for one call. It does *not* yet give the
coupling itself: the experiment's digests are selected adaptively, may have been queried in
advance by the adversary, and are correlated across signing requests, so the step from this
lemma to the independent-tape hypotheses still needs the presampling and
disclosure-tape arguments. No claim about the adaptive game is made here.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.FreshDigest

/-- An uncached call to the shared oracle answers uniformly on all thirty bytes. -/
theorem fresh_hash_uniform (input : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache input = none) :
    (simulateQ KeygenUniform.rom
        (Hashing.hash input : OracleComp OracleWorld HashOutput)).run' cache =
      ($ᵗ HashOutput : ProbComp HashOutput) := by
  unfold Hashing.hash
  rw [show simulateQ KeygenUniform.rom
      (query (spec := HashSpec) (m := OracleComp OracleWorld) input) =
    randomOracle input from roSim.simulateQ_HasQuery_query randomOracle _]
  rw [StateT.run'_eq, randomOracle, QueryImpl.withCaching_run_none _ hfresh]
  simp [uniformSampleImpl, Functor.map_map]

/-- A fresh `H_msg` call has a uniform parsed FORS view: the 63-bit instance and all
fourteen 12-bit leaf indices are jointly uniform and independent. -/
theorem fresh_messageDigest_parse_uniform (randomizer : Digest) (pk : PublicKey)
    (message : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache (Hashing.messageInput randomizer pk message) = none) :
    𝒟[MessageDigest.parse <$> (simulateQ KeygenUniform.rom
        (Hashing.messageDigest randomizer pk message :
          OracleComp OracleWorld HashOutput)).run' cache] =
      𝒟[($ᵗ MessageDigest.View : ProbComp MessageDigest.View)] := by
  have hrun : (simulateQ KeygenUniform.rom
      (Hashing.messageDigest randomizer pk message :
        OracleComp OracleWorld HashOutput)).run' cache =
      ($ᵗ HashOutput : ProbComp HashOutput) := by
    unfold Hashing.messageDigest
    exact fresh_hash_uniform _ cache hfresh
  rw [hrun]
  exact MessageDigest.evalDist_parse_uniform

end SlhDsaSecurity.FreshDigest

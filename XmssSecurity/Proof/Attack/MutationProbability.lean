import XmssSecurity.Proof.Attack.MutationPathCache
import XmssSecurity.Proof.Attack.PathBounds

/-! Exact root-collision probability for a uniformly replaced signature chain. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Attack

open Concrete

theorem mutationReplayPath_probability
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness) :
    Pr[fun result => result.1 ≠
        (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding).chainValue chain ∧
        result.2.1 = keyResult.1.1.root |
      Rom.randomHashPath
        (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
        0 (40 - (encoding chain).val) keyResult.2] =
      pathMutationProbability (40 - (encoding chain).val) := by
  have h := Rom.randomHashPath_distinct_hit_probability
    (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
    (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain))
    0 (mutationChainSteps (encoding chain) + 1 + treeHeight) keyResult.2
    (by
      intro i _ hi j _ hj hne left right
      exact mutationPathInput_separate _ _ _ _ _ _ i j (by omega) (by omega) hne left right)
    (by
      intro i _ hi
      exact mutationReplayInputs_honest keyResult hkey leafIndex chain encoding randomness i (by omega))
    (by
      intro i _ hi other hother
      exact mutationReplayInputs_fresh keyResult hkey leafIndex chain encoding randomness i
        (by omega) other hother)
  simp only [Nat.zero_add] at h
  rw [mutationHonestValue_start _ _ _ _ _ randomness,
    mutationHonestValue_root keyResult hkey] at h
  simpa only [mutationPath_length, pathMutationProbability] using h

/-- info: 'XmssSecurity.Attack.mutationReplayPath_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationReplayPath_probability

end XmssSecurity.Attack

import SlhDsaSecurity.Proof.CanonicalTarget
import SlhDsaSecurity.Proof.GrowthCharge

/-!
# The assembled structural term

This combines the three pieces that are now in place into the single bound the reduction
needs for every structural fault:

* `Extraction.*` turns any accepted forgery that deviates from the honest structure into a
  concrete witness — a deviating child tuple at some parent node whose hash reproduces that
  node's honest value;
* `CanonicalTarget.hit_of_deviating_collision` recognises exactly such a witness as a
  charged hit, and `CanonicalTarget.clean_of_canonical_cache` certifies that a cache built
  only from honest canonical queries starts clean;
* `GrowthCharge.prob_hitWithin_le` charges the whole phase at `limit / 2 ^ 128`, with the
  budget enforced by observable cache growth rather than a syntactic query bound.

The result, `prob_deviatingCollision_le`, says: in any charged phase started from a cache
holding only honest canonical queries, the probability that the phase ever produces a
deviating structural collision while growing the cache by at most `limit` is at most
`limit / 2 ^ 128`. The charge is linear in the budget and independent of how many honest
node values exist, which is what the `q / 2 ^ 127` target requires.

The remaining obligations are unaffected by this file: instantiating `initialCache` with
the actual post-key-generation, post-signing cache needs the honest phase shown to query
only canonical inputs, and the FORS coverage term and the framing-leak work bound are
separate.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.StructuralTerm

open CanonicalGraph

/-- The phase produced a child tuple deviating from the honest cells at some parent node,
whose cached answer nevertheless reproduces that node's honest value. This is precisely the
shape of every witness the structural extraction yields. -/
def DeviatingCollision {α : Type} (publicSeed : Digest) (cells : Cells) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ (candidates : Cells) (parent : StructuralNode) (output : HashOutput),
    (∃ child ∈ parent.children, candidates child ≠ cells child) ∧
    result.2 (canonicalInput publicSeed candidates parent) = some output ∧
    Hashing.truncate output = cells (.structural parent)

/-- A cache built only from honest canonical queries is clean for the canonical target, so
the charge applies to it. -/
theorem prob_hitWithin_canonicalTarget_le {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed : Digest) (cells : Cells) (limit : Nat) (initialCache : QueryCache HashSpec)
    (hcanonical : ∀ input, initialCache input ≠ none →
      ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent) :
    Pr[GrowthCharge.HitWithin (CanonicalTarget.canonicalTarget publicSeed cells)
        initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  GrowthCharge.prob_hitWithin_le computation
    (CanonicalTarget.canonicalTarget publicSeed cells) limit initialCache
    (CanonicalTarget.clean_of_canonical_cache publicSeed cells initialCache hcanonical)

/-- **The structural term.** Started from a cache of honest canonical queries, a charged
phase produces a deviating structural collision within a growth budget of `limit` with
probability at most `limit / 2 ^ 128`. -/
theorem prob_deviatingCollision_le {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed : Digest) (cells : Cells) (limit : Nat) (initialCache : QueryCache HashSpec)
    (hcanonical : ∀ input, initialCache input ≠ none →
      ∃ parent : StructuralNode, input = canonicalInput publicSeed cells parent) :
    Pr[fun result : α × QueryCache HashSpec =>
        DeviatingCollision publicSeed cells result ∧
          GrowthCharge.GrowthAtMost initialCache result.2 limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (prob_hitWithin_canonicalTarget_le computation publicSeed cells limit initialCache hcanonical)
  intro result _ hevent
  obtain ⟨⟨candidates, parent, output, hdeviates, hentry, hcollision⟩, hgrowth⟩ := hevent
  exact ⟨CanonicalTarget.hit_of_deviating_collision publicSeed cells candidates parent
    result output hdeviates hentry hcollision, hgrowth⟩

end SlhDsaSecurity.StructuralTerm

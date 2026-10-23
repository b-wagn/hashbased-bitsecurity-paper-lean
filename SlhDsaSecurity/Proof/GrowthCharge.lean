import SlhDsaSecurity.Proof.FreshHitBound

/-!
# Charging by observable cache growth

`FreshHitBound.prob_hit_le` needs a *syntactic* query bound, but the experiment supplies an
*almost-sure* bound on an instrumented counter (`Security.HasBudget`), and the two do not
match: an adversary meeting the counter bound need not meet a syntactic one.

This file closes that gap without any new instrumentation. Only a cache **miss** draws a
fresh uniform answer, so only a miss can newly hit a target; a replayed query cannot. The
number of misses during a run is exactly the growth of the cache, which is a function of
the observable final state. So the budget can be enforced by the *event* rather than by a
hypothesis on the computation:

  `Pr[Hit targetOf ∧ GrowthAtMost initialCache finalCache limit] ≤ limit / 2 ^ 128`.

`GrowthAtMost` avoids any cardinality notion on the infinite input type: it says no
duplicate-free list of inputs that are absent initially and present finally is longer than
`limit`. Cache monotonicity (`cache_mono`) supplies the "present finally" half for an entry
installed mid-run.

Repeated queries are *not* charged here, which is sound for an upper bound: a replay
returns the already-cached answer and cannot create a new hit. The experiment charges them,
so the experiment's budget dominates the growth, which is what makes this usable.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.GrowthCharge

/-- Cache entries are never *overwritten* either: an installed answer persists verbatim.

This is the strengthening of `cache_mono` that the partial-random-function invariant needs.
It is what makes a run started from the **empty** cache enough, where the `FreshFor`
hypothesis of the fresh-sampling results — freshness at the moment of the query — is not
available in the experiment, because the adversary may query a signer's input first. Once an
answer is installed, whoever installed it, every later query returns that same answer. -/
theorem cache_value_persists {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom computation).run initialCache))
    (input : Bytes) (output : HashOutput) (hentry : initialCache input = some output) :
    finalCache input = some output := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    have hmiddle : middleCache input = some output := by
      rcases queried with coin | queried
      · have hcache : middleCache = initialCache := by
          symm
          simpa [KeygenUniform.rom, Xmss.RandomOracleModel.impl, unifFwdImpl] using hquery
        exact hcache ▸ hentry
      · change (answer, middleCache) ∈ support ((randomOracle queried).run initialCache) at hquery
        cases hqueried : initialCache queried with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
          obtain ⟨sampled, _, hpair⟩ := hquery
          have hmid : middleCache = initialCache.cacheQuery queried sampled :=
            (Prod.ext_iff.mp hpair).2.symm
          rw [hmid]
          have hne : input ≠ queried := by
            intro hsame
            rw [hsame, hqueried] at hentry
            simp at hentry
          rw [QueryCache.cacheQuery_of_ne initialCache sampled hne]
          exact hentry
        | some cached =>
          rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
            Set.mem_singleton_iff] at hquery
          have hmid : middleCache = initialCache := (Prod.ext_iff.mp hquery).2
          exact hmid ▸ hentry
    exact ih answer middleCache finalCache result hrest hmiddle

/-! ## Pinning one coordinate

With `cache_value_persists`, the answer recorded at a given input is decided by whichever
query first missed on it, and never changes afterwards. That yields a bound charging only
**that one** miss, rather than every miss as `prob_badWithin_le` does: the cache value at a
fixed input hits a fixed target with probability at most `2 ^ -240`, independently of how
many queries the run makes.

Freshness is required only of the **starting** cache, which the experiment provides (it
begins empty). This is the point where the `FreshFor` obstruction — freshness at the moment
of the query, which adaptive prequeries deny — is avoided, and it is the single-coordinate
case of the partial-random-function invariant that the disclosure load cap needs.
-/

/-! ## Pinning many coordinates: the partial-random-function invariant

Generalising `prob_cache_value_le` from one coordinate to a finite set gives the invariant
the disclosure load cap needs: along any run started from a cache that is absent on a finite
set of inputs, the answers eventually recorded at those inputs behave as independent uniform
draws. Concretely, hitting one prescribed assignment costs `|HashOutput| ^ -|pinned|`.

Summing over a set of assignments then bounds any event defined by the recorded answers, in
particular "the FORS instances of the signed digests violate the load cap". The bound is an
inequality rather than an exact law, which is what makes it robust: the adversary may fail,
and distinct coordinates may be queried in any order and by either party.
-/

/-! ## The general charge

The charge does not depend on the bad event being "the answer truncates to a target": all it
needs is that each individual fresh answer is bad for its own input with probability at most
`p`. Stating it that way lets the same lemma carry both the structural term (bad = the answer
truncates to the canonical cell of the queried node) and the FORS coverage term (bad = the
answer parses to a digest whose fourteen FORS positions are all already disclosed).
-/

/-- Some cached answer is bad for its own input. -/
def Bad {α : Type} (bad : Bytes → HashOutput → Prop) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ input output, result.2 input = some output ∧ bad input output

/-- The cache holds no answer that is bad for its own input. -/
def CleanBad (bad : Bytes → HashOutput → Prop) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, cache input = some output → ¬ bad input output

theorem CleanBad.cacheQuery {bad : Bytes → HashOutput → Prop} {cache : QueryCache HashSpec}
    (hclean : CleanBad bad cache) {input : Bytes} {output : HashOutput}
    (hmiss : ¬ bad input output) : CleanBad bad (cache.cacheQuery input output) := by
  intro queried answer hanswer
  by_cases heq : queried = input
  · subst heq
    rw [QueryCache.cacheQuery_self] at hanswer
    cases hanswer
    exact hmiss
  · rw [QueryCache.cacheQuery_of_ne cache output heq] at hanswer
    exact hclean queried answer hanswer

end SlhDsaSecurity.GrowthCharge

import SlhDsaSecurity.Proof.Obligations
import SlhDsaSecurity.Proof.RandomiserProvenance
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.LazyBridge
import SlhDsaSecurity.Proof.WalkTable

/-!
# `SK.prf` has to be drawn after the walk, and what that costs the obligation's shape

`RandomiserProvenance.randomiserBad_source` reduces the randomiser defect to two things: the
adversary's own record holding an input of the `PRF_msg` class at the real seed, or the digest
overlap. The first is what `RandomizerGate.prob_run_randomizerInput_le` charges, and that charge
has one structural requirement which nothing below the obligation can supply:

    the secret is drawn **after** the run whose record is being charged.

`Obligations.SharedCharged` — and `Target.target_of_obligations`'s `hshared` with it — is stated
at a **fixed walk**, and the walk carries `SK.prf` as `walk.1.1.2.1`. The adversary is
quantified before the walk. So at that shape the secret is fixed before the adversary is chosen,
and the charge cannot be instantiated: not for want of a lemma, but because the statement is
false. `mem_support_withPrf` is the reason in one line — every walk stays in the support when
its `SK.prf` is replaced by *any* digest, keeping the same cells and the same cache, so the
per-walk bound is asserted at every value of the secret, with an adversary that may have been
written for one of them. An adversary whose first act is to hash a fixed `prf ‖ seed ‖ message`
makes `ReplayGate.RandomiserBad` certain on the walk carrying that pair, while the obligation
allows it `(q - 512 + 259) / 2 ^ 128`.

Nothing about the walk needs `SK.prf`, which is what makes the repair cheap. `Presample.worldWarmup`
is called at `sds.2.2` and `sds.1` only, so the walk's cells and cache are independent of it, and
the draw may be moved past the whole warm-up: `evalDist_resample_prf`. `probEvent_le_of_prfTail`
is then the drop-in replacement for `WarmedGame.probEvent_le_of_tail` that the charge can be
read against — a bound proved after every walk with `SK.prf` drawn *inside the tail* still
averages to a bound on the warmed run.

`prob_record_meets_prfClass_le` is the charge itself in the shape that presentation hands it,
with the record carried as a value of the run rather than existentially over its support.

What this file does **not** do, and what the deferral still needs, is recorded at the end of
`RandomiserDeferred`: with `SK.prf` deferred the run is still not independent of it, because the
signer derives each randomiser by querying `Hashing.randomizerInput SK.prf PK.seed framed`. That
is a second, separate obstacle, and it is a game hop rather than a presentation.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomiserDeferral

open Security CanonicalGraph WarmedGame

/-! ## `SK.prf` is a free parameter of the walk -/

/-- A walk with its `SK.prf` replaced. -/
def withPrf (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (prf : Digest) : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec :=
  (((walk.1.1.1, prf, walk.1.1.2.2), walk.1.2), walk.2)

@[simp] theorem withPrf_prf
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) (prf : Digest) :
    (withPrf walk prf).1.1.2.1 = prf := rfl

/-- **Replacing a walk's `SK.prf` keeps it in the support**, with the same cells and the same
cache. The warm-up reads only the public seed and the secret seed, so `SK.prf` never enters what
the walk leaves behind — it is carried along as a value and nothing more.

This is why a charge that must draw `SK.prf` after the run cannot be read at a fixed walk: the
walk fixes it, and fixes it *after* the adversary has been chosen. -/
theorem mem_support_withPrf
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (prf : Digest) :
    withPrf walk prf ∈ support graphWalk := by
  rw [graphWalk_eq] at hwalk ⊢
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hwalk ⊢
  obtain ⟨sds, -, result, hresult, hpair⟩ := hwalk
  subst hpair
  exact ⟨(sds.1, prf, sds.2.2), by simp [seeds], result, hresult, rfl⟩

/-- **And all but one replacement keeps the walk good.** `Target.GoodWalk`'s second clause
names the public seed and the walk's own root, neither of which moves; its first clause is the
seed coincidence, which is one unit of `2 ^ -128` and already in the assembly's allowance. -/
theorem goodWalk_withPrf
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hgood : Target.GoodWalk walk) {prf : Digest} (hne : prf ≠ walk.1.1.2.2) :
    Target.GoodWalk (withPrf walk prf) :=
  ⟨hne, hgood.2⟩

/-! ## The draw may be moved past the walk

`graphWalk` draws its three seeds and then evaluates the canonical graph at two of them. The
third may therefore be drawn at the end instead, and then — since nothing between reads it — be
replaced by a fresh draw after the walk has finished. -/

/-- The walk with its three draws written out. -/
theorem graphWalk_expand :
    graphWalk = (do
      let secret ← ($ᵗ Digest : ProbComp Digest)
      let prf ← ($ᵗ Digest : ProbComp Digest)
      let publicSeed ← ($ᵗ Digest : ProbComp Digest)
      let result ← (simulateQ randomOracle
        (CanonicalGraph.Programming.warmup publicSeed secret)).run ∅
      pure (((secret, prf, publicSeed), result.1), result.2)) := by
  rw [graphWalk_eq, seeds]
  simp [bind_assoc]

/-- The same walk with the `SK.prf` draw moved to the end. -/
noncomputable def lateWalk :
    ProbComp (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) := do
  let secret ← ($ᵗ Digest : ProbComp Digest)
  let publicSeed ← ($ᵗ Digest : ProbComp Digest)
  let result ← (simulateQ randomOracle
    (CanonicalGraph.Programming.warmup publicSeed secret)).run ∅
  let prf ← ($ᵗ Digest : ProbComp Digest)
  pure (((secret, prf, publicSeed), result.1), result.2)

/-- **The walk does not read `SK.prf`**, so its draw commutes past the warm-up. -/
theorem evalDist_graphWalk_late : 𝒟[graphWalk] = 𝒟[lateWalk] := by
  rw [graphWalk_expand, lateWalk]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun secret => ?_
  refine (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _).trans ?_
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun publicSeed => ?_
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-- **`SK.prf` may be redrawn after the walk.** -/
theorem evalDist_resample_prf :
    𝒟[graphWalk] = 𝒟[(do
      let walk ← graphWalk
      let prf ← ($ᵗ Digest : ProbComp Digest)
      pure (withPrf walk prf))] := by
  rw [evalDist_graphWalk_late, graphWalk_expand]
  simp only [bind_assoc, pure_bind, withPrf, lateWalk]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun secret => ?_
  exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    ($ᵗ Digest : ProbComp Digest) (by simp) _).symm

/-! ## The tail with `SK.prf` drawn inside it -/

/-- A bound that holds after every prefix holds over the whole run. The pairing form is
`Averaging.probEvent_bind_pair_le`; here the prefix's value is already carried by the
continuation, so nothing has to be paired back on. -/
theorem probEvent_bind_le {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : β → Prop) (bound : ℝ≥0∞)
    (hrest : ∀ value ∈ support first, Pr[event | rest value] ≤ bound) :
    Pr[event | first >>= rest] ≤ bound := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' value, Pr[= value | first] * Pr[event | rest value]
      ≤ ∑' value, Pr[= value | first] * bound := by
        refine ENNReal.tsum_le_tsum fun value => ?_
        by_cases hmem : value ∈ support first
        · exact mul_le_mul' le_rfl (hrest value hmem)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          exact zero_le
    _ = (∑' value, Pr[= value | first]) * bound := ENNReal.tsum_mul_right
    _ ≤ 1 * bound := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = bound := one_mul bound

/-- The counted game played from what the walk left, with `SK.prf` drawn first and kept. -/
noncomputable def prfTail (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    ProbComp (Digest × ((Outcome × Nat) × QueryCache HashSpec)) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let result ← tail adversary (withPrf walk prf)
  pure (prf, result)

/-- **A bound that holds after every walk with `SK.prf` deferred holds for the warmed run.**

This is `WarmedGame.probEvent_le_of_tail` with the one draw the charge needs moved inside the
tail. Everything else about the walk — its cells, its cache, its public seed, its root — is still
fixed before the adversary runs, so every charge that reads the walk as a fixed table reads it
unchanged. -/
theorem probEvent_le_of_prfTail (adversary : Adversary)
    (event : (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) ×
      QueryCache HashSpec → Prop) (bound : ℝ≥0∞)
    (htail : ∀ walk ∈ support graphWalk,
      Pr[fun pair : Digest × ((Outcome × Nat) × QueryCache HashSpec) =>
          event (((withPrf walk pair.1).1, pair.2.1), pair.2.2) | prfTail adversary walk] ≤
        bound) :
    Pr[event | warmedRun adversary] ≤ bound := by
  rw [warmedRun_eq, probEvent_map]
  have hlaw : 𝒟[(do
        let walk ← graphWalk
        let result ← tail adversary walk
        pure (walk, result))] =
      𝒟[graphWalk >>= fun walk =>
        (do
          let prf ← ($ᵗ Digest : ProbComp Digest)
          let result ← tail adversary (withPrf walk prf)
          pure (withPrf walk prf, result))] := by
    refine (LazyBridge.evalDist_bind_congr_right evalDist_resample_prf
      (fun walk => tail adversary walk >>= fun result => pure (walk, result))).trans ?_
    simp [bind_assoc]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
  refine probEvent_bind_le graphWalk _ _ bound fun walk hwalk => ?_
  have hmap : (do
      let prf ← ($ᵗ Digest : ProbComp Digest)
      let result ← tail adversary (withPrf walk prf)
      pure (withPrf walk prf, result)) =
      (fun pair : Digest × ((Outcome × Nat) × QueryCache HashSpec) =>
        (withPrf walk pair.1, pair.2)) <$> prfTail adversary walk := by
    rw [prfTail, map_eq_bind_pure_comp]
    simp [bind_assoc]
  rw [hmap, probEvent_map]
  exact htail walk hwalk

/-! ## The charge, in the shape the deferred presentation hands it

`RandomizerGate.prob_run_randomizerInput_le` is stated at a run that returns its own record.
What the game returns is an `Outcome`; the record is recovered from it by the recording writer
of `RecordedQueries`, which is a function of the run's value. So the charge is restated here
with the record as a *projection* of the run, which is the form a recorded presentation of the
tail supplies and the form `RandomiserProvenance.randomiserBad_source` asks for once its
existential is replaced by the run's own value. -/

/-- **The gate, charged against a record the run carries.** -/
theorem prob_record_meets_prfClass_le {α : Type} (run : ProbComp α)
    (record : α → Finset Bytes) (limit : Nat)
    (hlimit : ∀ result ∈ support run, (record result).card ≤ limit) :
    Pr[fun pair : α × Digest =>
        ∃ input ∈ record pair.1, RandomizerGate.PrfClass pair.2 input |
      (do
        let result ← run
        let prf ← ($ᵗ Digest : ProbComp Digest)
        pure (result, prf))] ≤
      (limit : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmapped := RandomizerGate.prob_run_randomizerInput_le
    ((fun result : α => (result, record result)) <$> run) limit ?_
  · rw [probEvent_bind_eq_tsum]
    rw [bind_map_left, probEvent_bind_eq_tsum] at hmapped
    refine le_trans (le_of_eq (tsum_congr fun result => congrArg _ ?_)) hmapped
    simp only [bind_pure_comp, probEvent_map]
    rfl
  · intro result hmem
    rw [support_map] at hmem
    obtain ⟨inner, hinner, hpair⟩ := hmem
    rw [← hpair]
    exact hlimit inner hinner

/-! ## What is left

With the two above in hand the randomiser half of `Obligations.SharedCharged` becomes a
statement about `prfTail`, and `RandomiserProvenance.randomiserBad_source` reduces it to the
record meeting the `PRF_msg` class, plus the digest overlap carried as a disjunct. Two things
still separate that from `prob_record_meets_prfClass_le`, and they are of different kinds.

* **A presentation.** The record has to be a value of the computation whose probability is being
  bounded. `RecordedQueries.recordedAfterSeeds` is that presentation for the *stripped* game and
  `RecordedQueries.map_recordedAfterSeeds` makes the recording invisible by an equality of
  computations; the same construction at `Scheme.keygenInternal` and `Scheme.sign` gives it for
  `WarmedGame.afterSeeds`, which is what `randomiserBad_source` is stated over. That is
  mechanical: `PhaseProvenance.exists_recorded_of_mem_countedRun` already carries the
  corresponding equality one level down.

* **A game hop.** Even with `SK.prf` drawn inside the tail, the tail is not independent of it:
  the signer derives each randomiser by querying `Hashing.randomizerInput SK.prf PK.seed framed`,
  so the record's law depends on the secret and the draw cannot simply be commuted past the run.
  The answers at those inputs are a random oracle's at inputs nobody else has queried — which is
  the event being charged — so the real game and the one whose signer draws its randomiser fresh
  are identical until that event, and the equality of its probability in the two is what keeps
  the charge from being paid twice. That equality is the analogue of
  `TrackedQueries.prob_meets_eq` for two *handlers* agreeing off a set, rather than for two
  caches; nothing in `BlindComparison` is stated at that generality yet. -/

/-! ## The crossing the randomiser charge needs

`WalkTable.probEvent_pairedRun_le` fixes `SK.prf` and the public seed and keeps the cell table in
the measure. That is the *input* half's shape, whose secret is the table. This charge's secret is
`SK.prf`, so the shape it needs is the opposite one: the table and the public seed fixed, and
`SK.prf` still in the measure.

Both come from the same presentation and for the same reason. `WalkTable.tablePairedRun` draws
all three explicitly and the three draws are independent, so whichever of them a charge has to
defer may be moved last. Here it is moved past the public seed and past the table, which is
`DeferredSampling.evalDist_bind_comm` twice and nothing else — the walk reads `SK.prf` nowhere,
as `mem_support_withPrf` says in the other presentation.

What the charge then faces is **not** a prf-free run: `WalkTable.walkOfTable prfSeed publicSeed
table` carries `SK.prf` in its seed triple, and the tail's signer derives every randomiser by
querying at it. Deferring the draw is necessary and not sufficient, and the hop that closes the
gap is `HandlerComparison.prob_bad_eq`. -/

/-- The run the randomiser charge reads: the public seed and the cell table fixed, `SK.prf`
drawn after both. -/
noncomputable def prfRun (adversary : Adversary) (publicSeed : Digest)
    (table : Cells × CanonicalGraph.Padding) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) := do
  let prfSeed ← ($ᵗ Digest : ProbComp Digest)
  let result ← tail adversary (WalkTable.walkOfTable prfSeed publicSeed table)
  pure (WalkTable.walkOfTable prfSeed publicSeed table, result)

/-- **A bound at each public seed and table, with `SK.prf` deferred, is a bound at the paired
run.** The counterpart of `WalkTable.probEvent_pairedRun_le` for a charge whose secret is
`SK.prf` rather than the cell table. -/
theorem probEvent_pairedRun_prf_le (adversary : Adversary)
    (event : ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) → Prop) (bound : ℝ≥0∞)
    (hinner : ∀ (publicSeed : Digest) (table : Cells × CanonicalGraph.Padding),
      Pr[event | prfRun adversary publicSeed table] ≤ bound) :
    Pr[event | Target.pairedRun adversary] ≤ bound := by
  classical
  have hlaw : 𝒟[WalkTable.tablePairedRun adversary] =
      𝒟[(do
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        let table ← ($ᵗ (Cells × CanonicalGraph.Padding) :
          ProbComp (Cells × CanonicalGraph.Padding))
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let result ← tail adversary (WalkTable.walkOfTable prfSeed publicSeed table)
        pure (WalkTable.walkOfTable prfSeed publicSeed table, result))] := by
    rw [WalkTable.tablePairedRun]
    refine (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _).trans ?_
    refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun publicSeed => ?_
    exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  rw [WalkTable.probEvent_pairedRun adversary event,
    probEvent_congr' (fun _ _ => Iff.rfl) hlaw]
  refine WalkDefects.probEvent_bind_le _ _ _ _ fun publicSeed => ?_
  refine WalkDefects.probEvent_bind_le _ _ _ _ fun table => ?_
  exact hinner publicSeed table

end SlhDsaSecurity.RandomiserDeferral

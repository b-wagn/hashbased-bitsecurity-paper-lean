import SlhDsaSecurity.Proof.KeygenUniform
import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.MessageDigest
import SlhDsaSecurity.Proof.ForsDisclosureTape

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

/-- An uncached short call answers uniformly on its sixteen retained bytes. This is
`KeygenUniform.fresh_tweakable_uniform` with the input left arbitrary, so it covers the
`PRF_msg` format as well as the tweakable ones. -/
theorem fresh_shortHash_uniform (input : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache input = none) :
    𝒟[(simulateQ KeygenUniform.rom
        (Hashing.shortHash input : OracleComp OracleWorld Digest)).run' cache] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hrun : (simulateQ KeygenUniform.rom
      (Hashing.shortHash input : OracleComp OracleWorld Digest)).run' cache =
      Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
    unfold Hashing.shortHash Hashing.hash
    simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_pure]
    rw [show simulateQ KeygenUniform.rom (query (spec := HashSpec)
        (m := OracleComp OracleWorld) input) =
      randomOracle input from roSim.simulateQ_HasQuery_query randomOracle _]
    change Prod.fst <$> ((randomOracle input).run cache >>=
      fun result => pure (Hashing.truncate result.1, result.2)) = _
    rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh]
    simp [uniformSampleImpl, Functor.map_map]
  rw [hrun]
  exact KeygenUniform.truncate_uniform

/-- The signer's randomizer is a uniform sixteen-byte value whenever its specified
`PRF_msg` byte input is absent from the cache. This is the hypothesis under which the
`H_msg` input that the signer goes on to query is unpredictable to the adversary; the
`FramingLeak` overlap is exactly the situation in which this hypothesis can fail, because
there the `PRF_msg` input coincides with an `H_msg` input the adversary may already have
queried. -/
theorem fresh_randomizer_uniform (prf seed : Digest) (message : Bytes)
    (cache : QueryCache HashSpec)
    (hfresh : cache (Hashing.randomizerInput prf seed message) = none) :
    𝒟[(simulateQ KeygenUniform.rom
        (Hashing.randomizer prf seed message : OracleComp OracleWorld Digest)).run' cache] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  unfold Hashing.randomizer
  exact fresh_shortHash_uniform _ cache hfresh

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

/-! ## The FORS instance of a fresh answer

The disclosure load cap is a statement about the FORS *instances* of the signed digests:
`ForsConcentration.uniform_load_tail_sharper_of_le` bounds, for iid uniform instance draws
into the `2 ^ 63` instances, the probability that `∑ i loads i ^ 14` exceeds `2 ^ 102`.

Connecting the oracle to that statement needs the pushforward `HashOutput → View → Instance`.
The first step is `MessageDigest.evalDist_parse_uniform`; the second is projection of a
uniform pair onto its first component. Composing them, the instance of a uniform thirty-byte
answer is uniform on the `2 ^ 63` FORS instances.
-/

/-- The FORS instance a thirty-byte answer parses to. -/
def instanceOf (output : HashOutput) : MessageDigest.Instance :=
  (MessageDigest.parse output).1

/-- A uniform answer has a uniform FORS instance. -/
theorem instanceOf_uniform :
    𝒟[instanceOf <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ MessageDigest.Instance : ProbComp MessageDigest.Instance)] := by
  have hmap : instanceOf <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    rw [Functor.map_map]
    rfl
  rw [hmap, evalDist_map, MessageDigest.evalDist_parse_uniform, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-- A fresh `H_msg` call therefore has a uniform FORS instance. This is the per-call input to
the load cap; the cap itself needs the joint law across the signed requests, which
`GrowthCharge.prob_cache_values_mem_le` supplies. -/
theorem fresh_messageDigest_instance_uniform (randomizer : Digest) (pk : PublicKey)
    (message : Bytes) (cache : QueryCache HashSpec)
    (hfresh : cache (Hashing.messageInput randomizer pk message) = none) :
    𝒟[instanceOf <$> (simulateQ KeygenUniform.rom
        (Hashing.messageDigest randomizer pk message :
          OracleComp OracleWorld HashOutput)).run' cache] =
      𝒟[($ᵗ MessageDigest.Instance : ProbComp MessageDigest.Instance)] := by
  have hrun : (simulateQ KeygenUniform.rom
      (Hashing.messageDigest randomizer pk message :
        OracleComp OracleWorld HashOutput)).run' cache =
      ($ᵗ HashOutput : ProbComp HashOutput) := by
    unfold Hashing.messageDigest
    exact fresh_hash_uniform _ cache hfresh
  rw [hrun]
  exact instanceOf_uniform

/-! ## Many coordinates at once

The load cap is a statement about the joint instance assignment of all signed requests, so
the per-answer pushforward has to be applied coordinatewise. It does preserve uniformity:
`MessageDigest.split` exhibits a thirty-byte answer as its parsed view together with the nine
bits the parser ignores, and the view is itself the instance together with the fourteen leaf
indices. Reassociating, a uniform answer is a uniform instance together with an independent
uniform remainder, and applying that coordinatewise turns a uniform assignment of answers
into a uniform assignment of instances.
-/

/-- Everything in a thirty-byte answer other than its FORS instance. -/
abbrev Remainder :=
  (MessageDigest.ForsTree → MessageDigest.ForsLeaf) × (BitVec 2 × BitVec 7)

/-- A thirty-byte answer as its instance together with the remainder. -/
def splitInstance (output : HashOutput) : MessageDigest.Instance × Remainder :=
  (instanceOf output, ((MessageDigest.parse output).2, (MessageDigest.split output).2))

theorem splitInstance_bijective : Function.Bijective splitInstance := by
  have hreassoc : Function.Bijective
      (fun pair : MessageDigest.View × (BitVec 2 × BitVec 7) =>
        (pair.1.1, (pair.1.2, pair.2)) : _ → MessageDigest.Instance × Remainder) := by
    refine ⟨fun left right hequal => ?_, fun target => ⟨((target.1, target.2.1), target.2.2), rfl⟩⟩
    obtain ⟨hfirst, hrest⟩ := Prod.mk.injEq _ _ _ _ |>.mp hequal
    obtain ⟨hsecond, hbits⟩ := Prod.mk.injEq _ _ _ _ |>.mp hrest
    exact Prod.ext (Prod.ext hfirst hsecond) hbits
  exact hreassoc.comp MessageDigest.split_bijective

/-- Coordinatewise, a uniform assignment of answers has a uniform assignment of instances. -/
theorem instanceAssignment_uniform (ι : Type) [Fintype ι] [DecidableEq ι] :
    𝒟[(fun assignment index => instanceOf (assignment index)) <$>
        ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))] =
      𝒟[($ᵗ (ι → MessageDigest.Instance) :
        ProbComp (ι → MessageDigest.Instance))] := by
  classical
  let coordinate : HashOutput ≃ MessageDigest.Instance × Remainder :=
    Equiv.ofBijective splitInstance splitInstance_bijective
  let regroup : (ι → HashOutput) ≃
      (ι → MessageDigest.Instance) × (ι → Remainder) :=
    (Equiv.piCongrRight (fun _ => coordinate)).trans
      (Equiv.arrowProdEquivProdArrow ι (fun _ => MessageDigest.Instance) (fun _ => Remainder))
  have hmap : (fun assignment : ι → HashOutput => fun index => instanceOf (assignment index))
        <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput)) =
      Prod.fst <$> (regroup <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))) := by
    rw [Functor.map_map]
    rfl
  have hinner : 𝒟[regroup <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))] =
      𝒟[($ᵗ ((ι → MessageDigest.Instance) × (ι → Remainder)) :
        ProbComp ((ι → MessageDigest.Instance) × (ι → Remainder)))] :=
    evalDist_map_bijective_uniform_cross (α := (ι → HashOutput))
      (β := ((ι → MessageDigest.Instance) × (ι → Remainder))) regroup regroup.bijective
  rw [hmap, evalDist_map, hinner, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-! ## From the oracle to a uniform instance assignment

Combining the charge with the pushforward: any event about the FORS instances of the answers
recorded at a finite set of pinned inputs is bounded by its probability under a uniform
instance assignment. The charge supplies the uniform counting measure over answer
assignments, and `instanceAssignment_uniform` transports it to instances.

This is the form the load cap is stated in, so it is the last step before
`ForsConcentration.uniform_load_tail_sharper_of_le` applies.
-/

open scoped Classical in
theorem prob_instance_event_le {α : Type} (computation : OracleComp OracleWorld α)
    (pinned : Finset Bytes) (cache : QueryCache HashSpec)
    (hfresh : ∀ x ∈ pinned, cache x = none)
    (instanceBad : (↥pinned → MessageDigest.Instance) → Prop) :
    Pr[fun result : α × QueryCache HashSpec =>
        ∃ assignment : ↥pinned → HashOutput,
          instanceBad (fun x => instanceOf (assignment x)) ∧
            ∀ x : ↥pinned, result.2 x.val = some (assignment x) |
      (simulateQ KeygenUniform.rom computation).run cache] ≤
      Pr[instanceBad |
        ($ᵗ (↥pinned → MessageDigest.Instance) :
          ProbComp (↥pinned → MessageDigest.Instance))] := by
  classical
  set bad : Finset (↥pinned → HashOutput) :=
    Finset.univ.filter (fun assignment => instanceBad (fun x => instanceOf (assignment x)))
    with hbad
  have hcharge := GrowthCharge.prob_cache_values_mem_le' computation pinned cache hfresh bad
  have hevent : Pr[fun result : α × QueryCache HashSpec =>
      ∃ assignment : ↥pinned → HashOutput,
        instanceBad (fun x => instanceOf (assignment x)) ∧
          ∀ x : ↥pinned, result.2 x.val = some (assignment x) |
    (simulateQ KeygenUniform.rom computation).run cache] ≤
      bad.card * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card := by
    refine le_trans (probEvent_mono ?_) hcharge
    intro result _ hexists
    obtain ⟨assignment, hinstance, hvalues⟩ := hexists
    exact ⟨assignment, by simp [hbad, hinstance], hvalues⟩
  refine hevent.trans ?_
  -- The uniform counting measure over answer assignments, transported to instances.
  have hcardFun : Fintype.card (↥pinned → HashOutput) =
      (Fintype.card HashOutput) ^ pinned.card := by
    rw [Fintype.card_fun, Fintype.card_coe]
  have hcount : (bad.card : ℝ≥0∞) *
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card =
      Pr[fun assignment : ↥pinned → HashOutput =>
        instanceBad (fun x => instanceOf (assignment x)) |
          ($ᵗ (↥pinned → HashOutput) : ProbComp (↥pinned → HashOutput))] := by
    rw [probEvent_uniformSample, hcardFun]
    push_cast
    rw [one_div, ← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul]
  rw [hcount]
  rw [show (fun assignment : ↥pinned → HashOutput =>
      instanceBad (fun x => instanceOf (assignment x))) =
    instanceBad ∘ (fun assignment index => instanceOf (assignment index)) from rfl,
    ← probEvent_map]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (instanceAssignment_uniform (↥pinned)))

/-! ## Landing on the disclosure tape

`ForsDisclosureTape.Tape requests` is `Fin requests → View`, and the disclosure results are
stated as `probEvent`s over a uniform tape — `ForsDisclosureTape.bad_load_probability_sharper`
for the load cap, and `ForsLeaveOneOut.independent_tape_coverage_le_sharper` for the whole
leave-one-out coverage bound. Transporting to full parsed *views* rather than only to
instances therefore lands exactly on those statements, and reuses them both.

The pushforward is the same argument as for instances, one step shorter: `MessageDigest.split`
already exhibits an answer as its view together with the nine ignored bits.
-/

/-- Coordinatewise, a uniform assignment of answers has a uniform assignment of parsed views. -/
theorem viewAssignment_uniform (ι : Type) [Fintype ι] [DecidableEq ι] :
    𝒟[(fun assignment index => MessageDigest.parse (assignment index)) <$>
        ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))] =
      𝒟[($ᵗ (ι → MessageDigest.View) : ProbComp (ι → MessageDigest.View))] := by
  classical
  let coordinate : HashOutput ≃ MessageDigest.View × (BitVec 2 × BitVec 7) :=
    Equiv.ofBijective MessageDigest.split MessageDigest.split_bijective
  let regroup : (ι → HashOutput) ≃
      (ι → MessageDigest.View) × (ι → BitVec 2 × BitVec 7) :=
    (Equiv.piCongrRight (fun _ => coordinate)).trans
      (Equiv.arrowProdEquivProdArrow ι (fun _ => MessageDigest.View)
        (fun _ => BitVec 2 × BitVec 7))
  have hmap : (fun assignment : ι → HashOutput =>
        fun index => MessageDigest.parse (assignment index))
        <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput)) =
      Prod.fst <$> (regroup <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))) := by
    rw [Functor.map_map]
    rfl
  have hinner : 𝒟[regroup <$> ($ᵗ (ι → HashOutput) : ProbComp (ι → HashOutput))] =
      𝒟[($ᵗ ((ι → MessageDigest.View) × (ι → BitVec 2 × BitVec 7)) :
        ProbComp ((ι → MessageDigest.View) × (ι → BitVec 2 × BitVec 7)))] :=
    evalDist_map_bijective_uniform_cross (α := (ι → HashOutput))
      (β := ((ι → MessageDigest.View) × (ι → BitVec 2 × BitVec 7))) regroup regroup.bijective
  rw [hmap, evalDist_map, hinner, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

open scoped Classical in
/-- Any event about the parsed views recorded at a finite set of pinned inputs is bounded by
its probability under a uniform assignment of views — that is, under a uniform disclosure
tape once the index is reindexed to `Fin`. -/
theorem prob_view_event_le {α : Type} (computation : OracleComp OracleWorld α)
    (pinned : Finset Bytes) (cache : QueryCache HashSpec)
    (hfresh : ∀ x ∈ pinned, cache x = none)
    (viewBad : (↥pinned → MessageDigest.View) → Prop) :
    Pr[fun result : α × QueryCache HashSpec =>
        ∃ assignment : ↥pinned → HashOutput,
          viewBad (fun x => MessageDigest.parse (assignment x)) ∧
            ∀ x : ↥pinned, result.2 x.val = some (assignment x) |
      (simulateQ KeygenUniform.rom computation).run cache] ≤
      Pr[viewBad |
        ($ᵗ (↥pinned → MessageDigest.View) :
          ProbComp (↥pinned → MessageDigest.View))] := by
  classical
  set bad : Finset (↥pinned → HashOutput) :=
    Finset.univ.filter
      (fun assignment => viewBad (fun x => MessageDigest.parse (assignment x))) with hbad
  have hcharge := GrowthCharge.prob_cache_values_mem_le' computation pinned cache hfresh bad
  have hevent : Pr[fun result : α × QueryCache HashSpec =>
      ∃ assignment : ↥pinned → HashOutput,
        viewBad (fun x => MessageDigest.parse (assignment x)) ∧
          ∀ x : ↥pinned, result.2 x.val = some (assignment x) |
    (simulateQ KeygenUniform.rom computation).run cache] ≤
      bad.card * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card := by
    refine le_trans (probEvent_mono ?_) hcharge
    intro result _ hexists
    obtain ⟨assignment, hview, hvalues⟩ := hexists
    exact ⟨assignment, by simp [hbad, hview], hvalues⟩
  refine hevent.trans ?_
  have hcardFun : Fintype.card (↥pinned → HashOutput) =
      (Fintype.card HashOutput) ^ pinned.card := by
    rw [Fintype.card_fun, Fintype.card_coe]
  have hcount : (bad.card : ℝ≥0∞) *
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card =
      Pr[fun assignment : ↥pinned → HashOutput =>
        viewBad (fun x => MessageDigest.parse (assignment x)) |
          ($ᵗ (↥pinned → HashOutput) : ProbComp (↥pinned → HashOutput))] := by
    rw [probEvent_uniformSample, hcardFun]
    push_cast
    rw [one_div, ← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul]
  rw [hcount]
  rw [show (fun assignment : ↥pinned → HashOutput =>
      viewBad (fun x => MessageDigest.parse (assignment x))) =
    viewBad ∘ (fun assignment index => MessageDigest.parse (assignment index)) from rfl,
    ← probEvent_map]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl)
    (viewAssignment_uniform (↥pinned)))

/-! ## Reindexing to the tape

`ForsDisclosureTape.Tape n` is indexed by `Fin n`, so the pinned inputs are reindexed through
`Finset.equivFin`. Reindexing along a bijection preserves uniformity, so the bound lands on a
uniform tape of exactly `pinned.card` entries, which is the form
`ForsDisclosureTape.bad_load_probability_sharper` and
`ForsLeaveOneOut.independent_tape_coverage_le_sharper` are stated in.
-/

open scoped Classical in
/-- Any event about the recorded views, read along a reindexing of the pinned inputs to
`Fin pinned.card`, is bounded by its probability under a uniform disclosure tape. -/
theorem prob_tape_event_le {α : Type} (computation : OracleComp OracleWorld α)
    (pinned : Finset Bytes) (cache : QueryCache HashSpec)
    (hfresh : ∀ x ∈ pinned, cache x = none)
    (tapeBad : ForsDisclosureTape.Tape pinned.card → Prop) :
    Pr[fun result : α × QueryCache HashSpec =>
        ∃ assignment : ↥pinned → HashOutput,
          tapeBad (fun i => MessageDigest.parse (assignment (pinned.equivFin.symm i))) ∧
            ∀ x : ↥pinned, result.2 x.val = some (assignment x) |
      (simulateQ KeygenUniform.rom computation).run cache] ≤
      Pr[tapeBad |
        ($ᵗ (ForsDisclosureTape.Tape pinned.card) :
          ProbComp (ForsDisclosureTape.Tape pinned.card))] := by
  classical
  refine le_trans (prob_view_event_le computation pinned cache hfresh
    (fun views => tapeBad (fun i => views (pinned.equivFin.symm i)))) ?_
  -- Reindexing along the bijection preserves uniformity.
  let reindex : (↥pinned → MessageDigest.View) ≃ ForsDisclosureTape.Tape pinned.card :=
    Equiv.arrowCongr pinned.equivFin (Equiv.refl MessageDigest.View)
  have hreindex : 𝒟[reindex <$> ($ᵗ (↥pinned → MessageDigest.View) :
        ProbComp (↥pinned → MessageDigest.View))] =
      𝒟[($ᵗ (ForsDisclosureTape.Tape pinned.card) :
        ProbComp (ForsDisclosureTape.Tape pinned.card))] :=
    evalDist_map_bijective_uniform_cross (α := (↥pinned → MessageDigest.View))
      (β := ForsDisclosureTape.Tape pinned.card) reindex reindex.bijective
  have hrewrite : (fun views : ↥pinned → MessageDigest.View =>
      tapeBad (fun i => views (pinned.equivFin.symm i))) = tapeBad ∘ reindex := rfl
  rw [hrewrite, ← probEvent_map]
  exact le_of_eq (probEvent_congr' (fun _ _ => Iff.rfl) hreindex)

end SlhDsaSecurity.FreshDigest

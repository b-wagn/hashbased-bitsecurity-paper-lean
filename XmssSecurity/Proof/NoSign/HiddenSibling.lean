import XmssSecurity.Proof.NoSign.RootSplit
import XmssSecurity.Proof.NoSign.Forwarding

/-!
# The hidden top sibling

An adversary without signing requests sees only the public key and the answers to its own hash
queries. Unless one of its queries is a key-generation input, it runs as from an empty cache
(`IdealCoupling.lean`), where its forgery depends on the root and the parameter only. The top
children of the tree are independent of the root (`RootSplit.lean`) and unpredictable
(`FreshOutput.lean`), and so is each key-generation input (`KeygenHit.lean`). Hence the forged
top sibling is the honest one with probability at most `(D + 1) / 2^128` for `D` direct hash
queries (`hiddenSibling_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.NoSign

/-- The forged top sibling is the honest one. -/
def HiddenSiblingGuessed (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (forgery : Forgery) : Prop :=
  forgery.signature.authPath topLevel =
    honestSibling cache secretKey.parameter secretKey.chainStart forgery.epoch

/-! ## Summation helpers -/

theorem probEvent_exists_mem_le {α β : Type} (computation : ProbComp α) (inputs : List β)
    (event : β → α → Prop) :
    Pr[fun a => ∃ input ∈ inputs, event input a | computation] ≤
      (inputs.map fun input => Pr[event input | computation]).sum := by
  induction inputs with
  | nil => simp
  | cons head tail ih =>
      calc
        _ ≤ Pr[fun a => event head a ∨ ∃ input ∈ tail, event input a | computation] :=
          probEvent_mono fun a _ ha => by simpa using ha
        _ ≤ Pr[event head | computation] +
              Pr[fun a => ∃ input ∈ tail, event input a | computation] :=
          probEvent_or_le _ _ _
        _ ≤ _ := by
          simp only [List.map_cons, List.sum_cons]
          gcongr

theorem probEvent_const_uniform {α : Type} [SampleableType α] (event : Prop) [Decidable event] :
    Pr[fun _ : α => event | $ᵗ α] = if event then 1 else 0 := by
  split_ifs with hevent
  · rw [probEvent_eq_one_iff]
    exact ⟨by simp, fun _ _ => hevent⟩
  · exact probEvent_eq_zero fun _ _ h => hevent h

/-! ## Events of the key-generation cache that ignore the root -/

/-- The two subtrees of key generation, with the chain starts. -/
noncomputable def subtrees (parameter : PublicParameter) :
    ProbComp ((LeafIndex → ChainIndex → Digest) ×
      (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec)) := do
  let secret ← Concrete.sampleSecret
  let left ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret (treeHeight - 1)
      (Concrete.childNode Concrete.rootNode false) : OracleComp HashSpec Digest)).run ∅
  let right ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret (treeHeight - 1)
      (Concrete.childNode Concrete.rootNode true) : OracleComp HashSpec Digest)).run left.2
  pure (secret, left, right)

/-- The key-generation cache with the top output `output`. -/
def splitCache (parameter : PublicParameter)
    (sample : (LeafIndex → ChainIndex → Digest) ×
      (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec))
    (output : HashOutput) : QueryCache HashSpec :=
  sample.2.2.2.cacheQuery (topInput parameter sample.2.1.1 sample.2.2.1) output

/-- Key generation with the chain starts, for a fixed parameter. -/
noncomputable def keygenTree (parameter : PublicParameter) :
    ProbComp ((LeafIndex → ChainIndex → Digest) × (Digest × QueryCache HashSpec)) := do
  let secret ← Concrete.sampleSecret
  let tree ← (simulateQ randomOracle
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest)).run ∅
  pure (secret, tree)

theorem evalDist_keygenTree_split (parameter : PublicParameter) :
    𝒟[keygenTree parameter] =
      𝒟[subtrees parameter >>= fun sample =>
        (fun output => (sample.1, (truncateHash output, splitCache parameter sample output))) <$>
          ($ᵗ HashOutput)] := by
  unfold keygenTree subtrees
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp]
  refine evalDist_bind_congr fun secret _ => ?_
  rw [evalDist_bind, evalDist_rootTree_split, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  rfl

/-- An event of the key-generation cache that does not depend on the root has the probability
of the same event with the root resampled. -/
theorem probEvent_subtrees_eq_keygenTree (parameter : PublicParameter)
    (event : (LeafIndex → ChainIndex → Digest) → QueryCache HashSpec → Prop)
    (hinvariant : ∀ sample ∈ support (subtrees parameter), ∀ output output',
      event sample.1 (splitCache parameter sample output) ↔
        event sample.1 (splitCache parameter sample output'))
    (output : HashOutput) :
    Pr[fun sample => event sample.1 (splitCache parameter sample output) | subtrees parameter] =
      Pr[fun result => event result.1 result.2.2 | keygenTree parameter] := by
  classical
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_keygenTree_split parameter),
    probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine tsum_congr fun sample => ?_
  by_cases hsample : sample ∈ support (subtrees parameter)
  · rw [probEvent_map]
    have hconst : Pr[(fun result : (LeafIndex → ChainIndex → Digest) ×
          (Digest × QueryCache HashSpec) => event result.1 result.2.2) ∘
          (fun output => (sample.1, (truncateHash output, splitCache parameter sample output))) |
          $ᵗ HashOutput] =
        Pr[fun _ : HashOutput => event sample.1 (splitCache parameter sample output) |
          $ᵗ HashOutput] :=
      probEvent_congr' (fun output' _ => hinvariant sample hsample output' output) rfl
    rw [hconst, probEvent_const_uniform]
    split_ifs <;> simp
  · rw [probOutput_eq_zero_of_not_mem_support hsample, zero_mul, ite_self]

/-- The honest top children in the split cache are the subtree outputs. -/
theorem honestChild_splitCache (parameter : PublicParameter)
    (sample : (LeafIndex → ChainIndex → Digest) ×
      (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec))
    (hsample : sample ∈ support (subtrees parameter)) (output : HashOutput) (right : Bool) :
    honestChild (splitCache parameter sample output) parameter sample.1 right =
      if right then sample.2.2.1 else sample.2.1.1 := by
  unfold subtrees at hsample
  simp only [bind_pure_comp, support_bind, support_map, Set.mem_iUnion, Set.mem_image,
    exists_prop] at hsample
  obtain ⟨secret, _, left, hleft, right', hright, rfl⟩ := hsample
  have hnone := topInput_none_of_subtrees parameter secret left right' hleft hright _
    (atHashAddress_topInput parameter left.1 right'.1)
  have hrightLe : right'.2 ≤ splitCache parameter (secret, left, right') output :=
    QueryCache.le_cacheQuery _ hnone
  have hleftLe : left.2 ≤ splitCache parameter (secret, left, right') output :=
    (Concrete.CacheReplay.randomOracle_cache_le _ left.2 right' hright).trans hrightLe
  unfold honestChild
  cases right
  · have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _ ∅ left.2 _
      left.1 hleft hleftLe
    rw [Concrete.CacheReplay.eval_treeNode] at heval
    simpa using heval
  · have heval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _ left.2
      right'.2 _ right'.1 hright hrightLe
    rw [Concrete.CacheReplay.eval_treeNode] at heval
    simpa using heval

theorem splitCache_ne_none_iff (parameter : PublicParameter)
    (sample : (LeafIndex → ChainIndex → Digest) ×
      (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec))
    (output : HashOutput) (input : HashInput) :
    splitCache parameter sample output input ≠ none ↔
      input = topInput parameter sample.2.1.1 sample.2.2.1 ∨ sample.2.2.2 input ≠ none := by
  unfold splitCache
  by_cases heq : input = topInput parameter sample.2.1.1 sample.2.2.1
  · subst input
    simp
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    simp [heq]

/-! ## The bounds for one parameter -/

theorem probEvent_keygenTree_honestSibling_le (parameter : PublicParameter)
    (leafIndex : LeafIndex) (target : Digest) :
    Pr[fun result : (LeafIndex → ChainIndex → Digest) × (Digest × QueryCache HashSpec) =>
        honestSibling result.2.2 parameter result.1 leafIndex = target |
      keygenTree parameter] ≤ digestInverse := by
  unfold keygenTree
  rw [probEvent_bind_eq_tsum]
  refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun secret _ => ?_
  rw [bind_pure_comp, probEvent_map]
  have hvalid : TreeSubtreeValid ((treeHeight - 1) + 1) Concrete.rootNode := by
    unfold TreeSubtreeValid Concrete.rootNode lifetime
    norm_num [treeHeight]
  exact probEvent_rootTree_treeNode_le parameter secret (treeHeight - 1) _ (by omega)
    (childNode_subtreeValid _ _ _ hvalid) target

theorem probEvent_subtrees_honestSibling_le (parameter : PublicParameter)
    (output : HashOutput) (leafIndex : LeafIndex) (target : Digest) :
    Pr[fun sample => honestSibling (splitCache parameter sample output) parameter sample.1
        leafIndex = target | subtrees parameter] ≤ digestInverse := by
  rw [probEvent_subtrees_eq_keygenTree parameter
    (fun secret cache => honestSibling cache parameter secret leafIndex = target)
    (fun sample hsample output output' => by
      simp only [honestSibling, honestChild_splitCache parameter sample hsample])]
  exact probEvent_keygenTree_honestSibling_le parameter leafIndex target

theorem probEvent_subtrees_cached_le (parameter : PublicParameter) (output : HashOutput)
    (input : HashInput) :
    Pr[fun sample => splitCache parameter sample output input ≠ none | subtrees parameter] ≤
      digestInverse := by
  rw [probEvent_subtrees_eq_keygenTree parameter (fun _ cache => cache input ≠ none)
    (fun sample _ output output' => by
      simp only [splitCache_ne_none_iff])]
  exact probEvent_keygenTree_cached_le parameter input

/-- For a fixed root output and a fixed run of the adversary from the empty cache with at most
`D` cached inputs, the honest key generation below the root makes the forged sibling honest, or
caches one of those inputs, with probability at most `(D + 1) / 2^128`. -/
theorem probEvent_subtrees_ideal_le (parameter : PublicParameter) (output : HashOutput)
    (forgery : Forgery) (finalCache : QueryCache HashSpec) (D : ℕ)
    (hinputs : ∃ inputs : List HashInput, inputs.length ≤ D ∧
      ∀ input, finalCache input ≠ none → input ∈ inputs) :
    Pr[fun sample =>
        HiddenSiblingGuessed (splitCache parameter sample output)
          (SecretKey.withoutPrecomputation parameter sample.1) forgery ∨
        HitsCache (splitCache parameter sample output) finalCache | subtrees parameter] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
  obtain ⟨inputs, hlength, hcover⟩ := hinputs
  calc
    _ ≤ Pr[fun sample => honestSibling (splitCache parameter sample output) parameter sample.1
            forgery.epoch = forgery.signature.authPath topLevel | subtrees parameter] +
          Pr[fun sample => ∃ input ∈ inputs,
            splitCache parameter sample output input ≠ none | subtrees parameter] := by
      refine (probEvent_mono fun sample _ hevent => ?_).trans (probEvent_or_le _ _ _)
      rcases hevent with hguess | ⟨input, hfinal, hcached⟩
      · exact Or.inl hguess.symm
      · exact Or.inr ⟨input, hcover input hfinal, hcached⟩
    _ ≤ digestInverse + (inputs.map fun input =>
          Pr[fun sample => splitCache parameter sample output input ≠ none |
            subtrees parameter]).sum :=
      add_le_add (probEvent_subtrees_honestSibling_le parameter output forgery.epoch _)
        (probEvent_exists_mem_le _ inputs _)
    _ ≤ digestInverse + inputs.length * digestInverse := by
      gcongr
      refine (List.sum_le_card_nsmul _ _ fun value hvalue => ?_).trans_eq
        (by rw [List.length_map, nsmul_eq_mul])
      obtain ⟨input, _, rfl⟩ := List.mem_map.mp hvalue
      exact probEvent_subtrees_cached_le parameter output input
    _ ≤ ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
      gcongr

end XmssSecurity.NoSign

namespace XmssSecurity.NoSign

/-! ## The game -/

/-- The adversary from the empty cache. -/
noncomputable def idealRun (adversary : Adversary) (publicKey : PublicKey) :
    ProbComp (Forgery × QueryCache HashSpec) :=
  (simulateQ romImpl (forwardPhase adversary publicKey)).run ∅

theorem adversaryPhase_le_ideal (adversary : Adversary) (hno : NoSignQueries adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
        HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
      (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
        keyResult.2] ≤
      Pr[fun result => HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 ∨
          HitsCache keyResult.2 result.2 | idealRun adversary keyResult.1.1] := by
  rw [adversaryPhase_eq_of_noSign adversary hno, simulateQ_map, StateT.run_map, probEvent_map]
  exact probEvent_run_le_empty (forwardPhase adversary keyResult.1.1) keyResult.2
    (HiddenSiblingGuessed keyResult.2 keyResult.1.2)

theorem idealRun_inputs (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (publicKey : PublicKey) (result : Forgery × QueryCache HashSpec)
    (hresult : result ∈ support (idealRun adversary publicKey)) :
    ∃ inputs : List HashInput, inputs.length ≤ D ∧
      ∀ input, result.2 input ≠ none → input ∈ inputs := by
  obtain ⟨inputs, hlength, hcover⟩ := exists_list_of_isQueryBoundP _ D
    (forwardPhase_isQueryBoundP adversary D hD publicKey) ∅ result hresult
  exact ⟨inputs, hlength, fun input hinput =>
    (hcover input hinput).resolve_left fun hempty => hempty rfl⟩

/-- An adversary without signing requests and with `D` direct hash queries forges the honest top
sibling with probability at most `(D + 1) / 2^128`. -/
theorem hiddenSibling_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hno : NoSignQueries adversary) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
          HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 |
        (simulateQ romImpl (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
  let event : (PublicKey × SecretKey) × QueryCache HashSpec →
      Forgery × QueryCache HashSpec → Prop := fun keyResult result =>
    HiddenSiblingGuessed keyResult.2 keyResult.1.2 result.1 ∨ HitsCache keyResult.2 result.2
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.keygen).run ∅] *
          Pr[event keyResult | idealRun adversary keyResult.1.1] :=
      ENNReal.tsum_le_tsum fun keyResult =>
        mul_le_mul' le_rfl (adversaryPhase_le_ideal adversary hno keyResult)
    _ = Pr[fun joint => event joint.1 joint.2 |
          (simulateQ romImpl Concrete.keygen).run ∅ >>= fun keyResult =>
            (fun result => (keyResult, result)) <$> idealRun adversary keyResult.1.1] := by
      rw [probEvent_bind_eq_tsum]
      refine tsum_congr fun keyResult => ?_
      rw [probEvent_map]
      rfl
    _ ≤ ((D + 1 : ℕ) : ℝ≥0∞) * digestInverse := by
      rw [keygen_run_eq]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum]
      refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun parameter _ => ?_
      -- The parameter fixed: resample the root and swap it with the adversary's run.
      let keyOf : (LeafIndex → ChainIndex → Digest) → Digest × QueryCache HashSpec →
          (PublicKey × SecretKey) × QueryCache HashSpec := fun secret tree =>
        ((⟨tree.1, parameter⟩, SecretKey.withoutPrecomputation parameter secret), tree.2)
      let observed : ProbComp (HashOutput × (Forgery × QueryCache HashSpec)) := do
        let output ← $ᵗ HashOutput
        let result ← idealRun adversary ⟨truncateHash output, parameter⟩
        pure (output, result)
      let finish : ((LeafIndex → ChainIndex → Digest) ×
          (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec)) →
          HashOutput × (Forgery × QueryCache HashSpec) →
          ((PublicKey × SecretKey) × QueryCache HashSpec) × (Forgery × QueryCache HashSpec) :=
        fun sample seen =>
          (keyOf sample.1 (truncateHash seen.1, splitCache parameter sample seen.1), seen.2)
      have hsplit :
          𝒟[Concrete.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealRun adversary (keyOf secret tree).1.1] =
          𝒟[subtrees parameter >>= fun sample => observed >>= fun seen =>
            pure (finish sample seen)] := by
        have hkeygen : (Concrete.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealRun adversary (keyOf secret tree).1.1) =
            keygenTree parameter >>= fun sampled =>
              (fun result => (keyOf sampled.1 sampled.2, result)) <$>
                idealRun adversary ⟨sampled.2.1, parameter⟩ := by
          simp only [keygenTree, bind_assoc, pure_bind]
          rfl
        rw [hkeygen, evalDist_bind, evalDist_keygenTree_split, ← evalDist_bind]
        simp only [observed, finish, keyOf, bind_assoc, map_eq_bind_pure_comp, pure_bind,
          Function.comp_apply]
        rfl
      rw [probEvent_congr' (fun _ _ => Iff.rfl) hsplit, probEvent_bind_bind_swap,
        probEvent_bind_eq_tsum]
      refine tsum_probOutput_mul_le_of_mem_support _ _ _ fun seen hseen => ?_
      have hresult : seen.2 ∈ support (idealRun adversary ⟨truncateHash seen.1, parameter⟩) := by
        simp only [observed, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          exists_prop] at hseen
        obtain ⟨output, _, result, hresult, rfl⟩ := hseen
        exact hresult
      rw [bind_pure_comp, probEvent_map]
      exact probEvent_subtrees_ideal_le parameter seen.1 seen.2.1 seen.2.2 D
        (idealRun_inputs adversary D hD _ seen.2 hresult)

end XmssSecurity.NoSign

import XmssSecurity.Proof.Checksum.NoSign.HiddenSibling
import XmssSecurity.Proof.Checksum.Direct.DecidingCollision
import XmssSecurity.Proof.Checksum.Direct.DecidingVerifierCount
import XmssSecurity.Proof.Checksum.MerkleVerificationQueryPresence
import XmssSecurity.Proof.Checksum.Direct.DecidingSecondLane

/-!
# The top query of an accepted forgery

An accepted forgery ends with a top query whose output is the root. Either that query is the
honest top query of key generation, and then the forged top sibling is the honest one
(`HiddenSiblingGuessed`), or it is a different input at the top address, first queried by the
adversary or by the verifier, whose fresh output collides with the root (`topCases`). The
adversary makes at most `D` top queries and the verifier one, so the collision has probability at
most `(D + 1) / 2^128` (`topFresh_le`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

/-! ## The verifier queries the top address once -/

theorem not_top_of_domain_ne (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (hne : domain ≠ .merkle topLevel Concrete.rootNode) :
    ¬ AtHashAddress parameter (.merkle topLevel Concrete.rootNode)
      (tweakableHashInput parameter domain payload) := by
  rw [atHashAddress_tweakableHashInput_iff]
  exact hne

theorem authenticationRoot_top_zero (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    ∀ levels, levels ≤ treeHeight - 1 →
      (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
        OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle topLevel Concrete.rootNode)) 0 := by
  intro levels
  induction levels with
  | zero =>
      intro _
      simp [Concrete.authenticationRoot]
  | succ levels ih =>
      intro hlevels
      rw [Concrete.authenticationRoot]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (ih (by omega)) fun current _ => ?_
      unfold Concrete.authenticationNodeHash
      split
      · have hne : ∀ node : MerkleNode, ∀ hlevel : levels < treeHeight,
            HashDomain.merkle ⟨levels, hlevel⟩ node ≠ .merkle topLevel Concrete.rootNode := by
          intro node hlevel heq
          simp only [HashDomain.merkle.injEq, topLevel, Fin.mk.injEq] at heq
          omega
        split
        · exact Deciding.tweakableHash_isQueryBoundP_zero _ _ _ _
            (not_top_of_domain_ne _ _ _ (hne _ _))
        · exact Deciding.tweakableHash_isQueryBoundP_zero _ _ _ _
            (not_top_of_domain_ne _ _ _ (hne _ _))
      · simp

theorem authenticationRoot_top_one (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) (levels : ℕ) (hlevels : levels ≤ treeHeight) :
    (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.merkle topLevel Concrete.rootNode)) 1 := by
  cases levels with
  | zero => simp [Concrete.authenticationRoot]
  | succ levels =>
      rw [Concrete.authenticationRoot]
      exact (OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
        (authenticationRoot_top_zero _ _ _ _ levels (by omega)) fun _ _ =>
          Deciding.authenticationNodeHash_isQueryBoundP_one _ _ _ _ _ _).mono (by norm_num)

theorem verifyAfterLeaf_top_one (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool).IsQueryBoundP
      (AtHashAddress publicKey.parameter (.merkle topLevel Concrete.rootNode)) 1 := by
  unfold Concrete.verifyAfterLeaf
  have hlevels : treeHeight ≤ treeHeight := le_rfl
  generalize hgen : treeHeight = levels at hlevels ⊢
  have hroot := authenticationRoot_top_one publicKey.parameter leafIndex signature leaf
    levels (hgen ▸ hlevels)
  have hbind := OracleComp.isQueryBoundP_bind (m := 0) hroot
    (ob := fun root => (pure (decide (root = publicKey.root)) : OracleComp HashSpec Bool))
    (fun _ _ => isQueryBoundP_pure _ _ _)
  rw [Nat.add_zero] at hbind
  exact hbind

theorem verify_top_one (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (signature : Signature) :
    (Concrete.verify publicKey leafIndex message signature :
      OracleComp HashSpec Bool).IsQueryBoundP
      (AtHashAddress publicKey.parameter (.merkle topLevel Concrete.rootNode)) 1 := by
  unfold Concrete.verify
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
    (Deciding.tweakableHash_isQueryBoundP_zero _ _ _ _
      (not_top_of_domain_ne _ _ _ (by simp))) fun digest _ => ?_).mono (by norm_num)
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 1) ?_ fun endpoints _ => ?_).mono
    (by norm_num)
  · unfold Concrete.recoverEndpoints
    exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
      Deciding.chainWalk_isQueryBoundP_zero _ _ _ _ _ _ _ fun step value =>
        not_top_of_domain_ne _ _ _ (by simp)
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 1)
    (Deciding.tweakableHash_isQueryBoundP_zero _ _ _ _
      (not_top_of_domain_ne _ _ _ (by simp))) fun leaf _ => ?_).mono (by norm_num)
  exact verifyAfterLeaf_top_one publicKey leafIndex signature leaf

theorem scheme_verify_top_one (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (Concrete.scheme.verify publicKey leafIndex message signature).IsQueryBoundP
      (Rom.IsRelevantHashQuery
        (AtHashAddress publicKey.parameter (.merkle topLevel Concrete.rootNode))) 1 := by
  classical
  change (liftComp (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := AtHashAddress publicKey.parameter (.merkle topLevel Concrete.rootNode))
    (fun _ => Iff.rfl) (verify_top_one publicKey leafIndex message signature)

/-! ## Moving top queries to the honest one -/

/-- Every input at the top address, moved to the honest top input. -/
noncomputable def topTarget (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : HashInput :=
  if AtHashAddress secretKey.parameter (.merkle topLevel Concrete.rootNode) input then
    topInput secretKey.parameter
      (honestChild cache secretKey.parameter secretKey.chainStart false)
      (honestChild cache secretKey.parameter secretKey.chainStart true)
  else input

theorem atTop_of_topTarget_ne (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (hmoved : topTarget secretKey cache input ≠ input) :
    AtHashAddress secretKey.parameter (.merkle topLevel Concrete.rootNode) input := by
  unfold topTarget at hmoved
  split_ifs at hmoved with hat
  · exact hat
  · exact absurd rfl hmoved

theorem expected_top_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hno : NoSignQueries adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hparam : keyResult.1.1.parameter = keyResult.1.2.parameter) :
    expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input => topTarget keyResult.1.2 keyResult.2 input ≠ input)
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Deciding.verificationPhase keyResult.1.1 keyResult.1.2) keyResult.2 ≤ D + 1 := by
  classical
  let atTop := Rom.IsRelevantHashQuery
    (AtHashAddress keyResult.1.2.parameter (.merkle topLevel Concrete.rootNode))
  calc
    _ ≤ expectedSimulatedQueryCount romImpl atTop
          (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
            Deciding.verificationPhase keyResult.1.1 keyResult.1.2) keyResult.2 := by
      refine expectedSimulatedQueryCount_mono romImpl _ _ (fun input hinput => ?_) _ _
      rcases input with _ | hashInput
      · exact hinput.elim
      · exact atTop_of_topTarget_ne keyResult.1.2 keyResult.2 hashInput hinput
    _ = expectedSimulatedQueryCount romImpl atTop
          (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 +
        ∑' prefixResult, Pr[= prefixResult | (simulateQ romImpl
            (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2] *
          expectedSimulatedQueryCount romImpl atTop
            (Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)
            prefixResult.2 :=
      expectedSimulatedQueryCount_bind romImpl _ _ _ _
    _ ≤ D + 1 := by
      refine add_le_add ?_ ?_
      · rw [adversaryPhase_eq_of_noSign adversary hno, expectedSimulatedQueryCount_map]
        refine expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ _ D ?_
        refine (forwardPhase_isQueryBoundP adversary D hD keyResult.1.1).of_imp ?_
        intro input hinput
        rcases input with _ | _
        · exact hinput.elim
        · trivial
      · refine Direct.tsum_probOutput_mul_le _ _ _ fun prefixResult => ?_
        rw [Deciding.expectedQueries_verificationPhase_eq]
        have hbound := scheme_verify_top_one keyResult.1.1 prefixResult.1.1.epoch
          prefixResult.1.1.message prefixResult.1.1.signature
        rw [hparam] at hbound
        exact_mod_cast expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ _ 1 hbound

end XmssSecurity.Checksum.NoSign

namespace XmssSecurity.Checksum.NoSign

/-! ## The case split on the top query -/

theorem nodeIndex_top (leafIndex : LeafIndex) :
    Concrete.nodeIndex leafIndex topLevel.val = Concrete.rootNode := by
  apply Fin.ext
  simp only [Concrete.nodeIndex, Concrete.rootNode, topLevel]
  apply Nat.div_eq_of_lt
  have hlt := leafIndex.isLt
  simpa [lifetime, treeHeight] using hlt

theorem rootNode_lt_top : Concrete.rootNode.val < 2 ^ (treeHeight - (topLevel.val + 1)) := by
  simp [Concrete.rootNode, topLevel, treeHeight]

/-- An accepted forgery's top query is the honest one, which reveals the honest top sibling,
or a fresh input at the top address whose output collides with the root. -/
theorem topCases (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run
        prefixResult.2))
    (hwin : execution.1.won = true) :
    HiddenSiblingGuessed keyResult.2 keyResult.1.2 prefixResult.1.1 ∨
      Rom.AdaptiveFreshDigestCollisionWith keyResult.2 execution.2
        (topTarget keyResult.1.2 keyResult.2) := by
  classical
  have hprecomp : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hprecomp
  have hfull := Deciding.afterKeygen_of_phases adversary keyResult.1.1 keyResult.1.2
    keyResult.2 prefixResult hprefix execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hfull
  have hcons := capped_detailed_execution_consistent adversary execution hgame
  obtain ⟨hpk, hsk, hforgery, -, hverifyRun⟩ :=
    Deciding.verificationPhase_support _ _ _ _ _ hafter
  have hparam := Deciding.keygen_publicKey_parameter_eq keyResult hkeygen
  have hKF : keyResult.2 ≤ execution.2 :=
    (xmssRom_cache_le _ _ _ hprefix).trans (xmssRom_cache_le _ _ _ hafter)
  have hverified : execution.1.verified = true :=
    ((GameOutcome.won_eq_true_iff _).mp hwin).2.2
  -- Acceptance, read off the final cache.
  have hfromCache : Concrete.verifyFromCache execution.2 keyResult.1.1 prefixResult.1.1.epoch
      prefixResult.1.1.message prefixResult.1.1.signature = true := by
    have hverification := hcons.verification
    rw [hverified, hpk, hforgery] at hverification
    exact hverification.symm
  obtain ⟨encoding, hdecode, hascend⟩ :=
    (Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hfromCache
  -- The verifier's run caches its top query.
  have hrunRO : (true, execution.2) ∈ support ((simulateQ randomOracle
      (Concrete.verify keyResult.1.1 prefixResult.1.1.epoch prefixResult.1.1.message
        prefixResult.1.1.signature : OracleComp HashSpec Bool)).run prefixResult.2) := by
    have hroute : simulateQ romImpl (Concrete.scheme.verify keyResult.1.1 prefixResult.1.1.epoch
          prefixResult.1.1.message prefixResult.1.1.signature) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.verify keyResult.1.1 prefixResult.1.1.epoch prefixResult.1.1.message
            prefixResult.1.1.signature : OracleComp HashSpec Bool) := by
      change simulateQ (unifFwdImpl HashSpec +
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
        (liftM (Concrete.verify keyResult.1.1 prefixResult.1.1.epoch prefixResult.1.1.message
          prefixResult.1.1.signature : OracleComp HashSpec Bool)) = _
      exact QueryImpl.simulateQ_add_liftM_right _ _ _
    have h := hverifyRun
    rw [hverified, hroute] at h
    exact h
  obtain ⟨leafCache, leaf, rootCache, rootDigest, hrootRun, hrootLe, hleafEq⟩ :=
    Concrete.CacheReplay.verify_true_authenticationRoot_support_in_largerCache keyResult.1.1
      prefixResult.1.1.epoch prefixResult.1.1.message prefixResult.1.1.signature encoding
      prefixResult.2 execution.2 execution.2 hrunRO hdecode le_rfl
  obtain ⟨output, houtput⟩ :=
    Concrete.CacheReplay.authenticationRoot_query_cached_as_in_largerCache
      keyResult.1.1.parameter prefixResult.1.1.epoch prefixResult.1.1.signature treeHeight leaf
      topLevel topLevel.isLt le_rfl leafCache rootCache execution.2 rootDigest
      hrootRun hrootLe
  -- The verifier's top input and the honest one.
  let current := Merkle.ascend (Concrete.CacheView.nodeHash execution.2 keyResult.1.1.parameter
    prefixResult.1.1.epoch) (Concrete.signaturePath prefixResult.1.1.signature) 0 topLevel.val
    leaf
  let verifierInput := Concrete.CacheView.nodeInput keyResult.1.1.parameter
    prefixResult.1.1.epoch topLevel current
    (Concrete.signaturePath prefixResult.1.1.signature topLevel.val)
  let honestInput := topInput keyResult.1.2.parameter
    (honestChild keyResult.2 keyResult.1.2.parameter keyResult.1.2.chainStart false)
    (honestChild keyResult.2 keyResult.1.2.parameter keyResult.1.2.chainStart true)
  have hverifierCached : execution.2 verifierInput = some output := hrootLe houtput
  have hverifierAt : AtHashAddress keyResult.1.2.parameter (.merkle topLevel Concrete.rootNode)
      verifierInput := by
    simp only [verifierInput, Concrete.CacheView.nodeInput, hparam,
      atHashAddress_tweakableHashInput_iff, nodeIndex_top]
  obtain ⟨honestOutput, hhonest⟩ := Concrete.keygen_cache_has_merkleInput _ hold topLevel
    Concrete.rootNode rootNode_lt_top
  have hhonest' : keyResult.2 honestInput = some honestOutput := hhonest
  have hchildren := Concrete.precomputedKeygen_merkleChildren_eq_of_cache_le keyResult hprecomp
    execution.2 hKF topLevel Concrete.rootNode rootNode_lt_top
  -- The digests of both inputs are the root.
  have hverifierDigest : Concrete.CacheView.digestAt execution.2 verifierInput =
      keyResult.1.1.root := by
    rw [← hascend, hleafEq]
    rw [show treeHeight = topLevel.val + 1 from rfl]
    simp only [Merkle.ascend, zero_add]
    rw [Concrete.CacheView.nodeHash_eq _ _ _ _ _ _ topLevel.isLt]
  have hhonestDigest : Concrete.CacheView.digestAt execution.2 honestInput =
      keyResult.1.1.root := by
    have hkey := hcons.key
    rw [hpk, hsk] at hkey
    rw [hkey]
    unfold Concrete.CacheReplay.publicKeyFromCache
    dsimp only
    rw [show Concrete.CacheReplay.treeNode execution.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart treeHeight Concrete.rootNode =
      Concrete.CacheReplay.treeNode execution.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart (topLevel.val + 1) Concrete.rootNode from rfl,
      Concrete.CacheReplay.treeNode_succ_eq, dif_pos topLevel.isLt]
    obtain ⟨hleftChild, hrightChild⟩ := Prod.mk.injEq _ _ _ _ ▸ hchildren
    simp only [topLevel] at hleftChild hrightChild
    simp only [honestInput, honestChild, topInput, Concrete.CacheView.merkleHash, hleftChild,
      hrightChild]
    rfl
  by_cases hsame : verifierInput = honestInput
  · -- The verifier recomputed the honest top input: the forged sibling is honest.
    left
    have hpayload := payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter
      (.merkle topLevel Concrete.rootNode) (by
        have h := hsame
        simp only [verifierInput, honestInput, Concrete.CacheView.nodeInput, topInput,
          Concrete.CacheView.merkleInput, hparam, nodeIndex_top] at h
        exact h)
    have hsibling : Concrete.signaturePath prefixResult.1.1.signature topLevel.val =
        prefixResult.1.1.signature.authPath topLevel := by
      simp [Concrete.signaturePath, topLevel.isLt]
    unfold HiddenSiblingGuessed honestSibling
    rw [← hsibling]
    unfold Concrete.CacheView.authenticationNodePayload at hpayload
    cases hbit : prefixResult.1.1.epoch.val.testBit (treeHeight - 1)
    · simp only [topLevel, hbit, Bool.false_eq_true, if_false] at hpayload
      exact (Prod.ext_iff.mp (Concrete.nodePayload_injective (a₁ := (_, _)) (a₂ := (_, _))
        hpayload)).2
    · simp only [topLevel, hbit, if_true] at hpayload
      exact (Prod.ext_iff.mp (Concrete.nodePayload_injective (a₁ := (_, _)) (a₂ := (_, _))
        hpayload)).1
  · -- A different top input with the root as its output: a fresh collision.
    right
    refine ⟨verifierInput, output, honestOutput, hverifierCached, ?_, ?_, ?_⟩
    · cases hcached : keyResult.2 verifierInput with
      | none => rfl
      | some other =>
          exfalso
          apply hsame
          exact Concrete.keygen_cache_unique_merkleAddress _ hold topLevel Concrete.rootNode
            verifierInput honestInput other honestOutput hverifierAt
            (atHashAddress_topInput _ _ _) hcached hhonest'
    · rw [show topTarget keyResult.1.2 keyResult.2 verifierInput = honestInput by
        unfold topTarget
        rw [if_pos hverifierAt]]
      exact hhonest'
    · rw [show topTarget keyResult.1.2 keyResult.2 verifierInput = honestInput by
        unfold topTarget
        rw [if_pos hverifierAt]]
      rw [hverifierDigest, hhonestDigest]

end XmssSecurity.Checksum.NoSign

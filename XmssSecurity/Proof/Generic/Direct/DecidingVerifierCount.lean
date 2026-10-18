import XmssSecurity.Proof.Generic.Direct.Deciding
import XmssSecurity.Proof.Generic.Direct.VerifierBound
import XmssSecurity.Proof.Generic.Direct.Structural

/-!
# The verifier's queries on the deciding path

One verification at leaf index `idx*` makes at most `decidingQueryBound = 7 + 1 + 32 = 40` hash
queries whose input is a deciding input for `idx*` and a fixed chain `i0`, whatever the oracle
answers: the encoding hash is never a deciding input (encoding domain); the chain walk of chain
`i0` has at most `chainLength - 1 = 7` steps and the walks of the other chains query only inputs
of their own chain domain; the leaf hash is one query; the `32` Merkle levels are `32` queries.
The bound is stated syntactically (`IsQueryBoundP`) for an arbitrary predicate implying
`IsDecidingInput`, lifted to the random-oracle world for the predicate "moved by
`decidingTargetInput`", and turned into a bound on the expected simulated query count.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete

set_option backward.isDefEq.respectTransparency false

/-- The deciding queries of one verification: `7` chain steps of the deciding chain, the leaf
hash, and the `32` Merkle levels. -/
def decidingQueryBound : ℕ := (chainLength - 1) + 1 + treeHeight

theorem decidingQueryBound_eq : decidingQueryBound = 40 := by decide

/-! ## Which tweakable-hash inputs are deciding -/

/-- A deciding input built from `tweakableHashInput` has a chain domain of the deciding chain, the
leaf domain, or a Merkle domain on the path of the leaf index. -/
theorem domain_of_isDecidingInput_tweakableHashInput (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (domain : HashDomain) (payload : HashInput)
    (h : IsDecidingInput parameter leafIndex chain (tweakableHashInput parameter domain payload)) :
    (∃ step : ChainStep, domain = .chain leafIndex chain step) ∨
      domain = .leaf leafIndex ∨
      (∃ level : MerkleLevel, domain = .merkle level (Concrete.nodeIndex leafIndex level.val)) := by
  rcases h with ⟨step, value, heq⟩ | ⟨endpoints, heq⟩ | ⟨level, left, right, heq⟩
  · exact Or.inl ⟨step, domain_eq_of_tweakableHashInput_eq parameter heq⟩
  · exact Or.inr (Or.inl (domain_eq_of_tweakableHashInput_eq parameter heq))
  · exact Or.inr (Or.inr ⟨level, domain_eq_of_tweakableHashInput_eq parameter heq⟩)

theorem not_isDecidingInput_encoding (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (leafIndex' : LeafIndex) (payload : HashInput) :
    ¬IsDecidingInput parameter leafIndex chain
      (tweakableHashInput parameter (.encoding leafIndex') payload) := by
  intro h
  rcases domain_of_isDecidingInput_tweakableHashInput parameter leafIndex chain _ _ h with
    ⟨step, heq⟩ | heq | ⟨level, heq⟩ <;> cases heq

theorem not_isDecidingInput_chain_ne (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (leafIndex' : LeafIndex) (chain' : ChainIndex) (step : ChainStep)
    (payload : HashInput) (hne : chain' ≠ chain) :
    ¬IsDecidingInput parameter leafIndex chain
      (tweakableHashInput parameter (.chain leafIndex' chain' step) payload) := by
  intro h
  rcases domain_of_isDecidingInput_tweakableHashInput parameter leafIndex chain _ _ h with
    ⟨step', heq⟩ | heq | ⟨level, heq⟩
  · cases heq
    exact hne rfl
  · cases heq
  · cases heq

/-! ## The building blocks, for an arbitrary predicate -/

section Generic

variable (p : HashInput → Prop) [DecidablePred p]

theorem tweakableHash_isQueryBoundP_one (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      p 1 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash]

theorem tweakableHash_isQueryBoundP_zero (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (hnot : ¬p (tweakableHashInput parameter domain payload)) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      p 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, hnot]

theorem chainWalk_isQueryBoundP_steps (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p steps := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 1) ih ?_
      intro previous _
      split
      · exact tweakableHash_isQueryBoundP_one p _ _ _
      · simp

theorem chainWalk_isQueryBoundP_zero (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position steps : Nat) (value : Digest)
    (hnot : ∀ (step : ChainStep) (value : Digest),
      ¬p (tweakableHashInput parameter (.chain leafIndex chain step) (Concrete.digestBytes value))) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ih ?_
      intro previous _
      split
      · exact tweakableHash_isQueryBoundP_zero p _ _ _ (hnot _ _)
      · simp

theorem authenticationNodeHash_isQueryBoundP_one (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (current sibling : Digest) :
    (Concrete.authenticationNodeHash parameter leafIndex level current sibling :
      OracleComp HashSpec Digest).IsQueryBoundP p 1 := by
  unfold Concrete.authenticationNodeHash
  split
  · split
    · exact tweakableHash_isQueryBoundP_one p _ _ _
    · exact tweakableHash_isQueryBoundP_one p _ _ _
  · simp

theorem authenticationRoot_isQueryBoundP_levels (parameter : PublicParameter)
    (leafIndex : LeafIndex) (signature : Signature) (levels : Nat) (leaf : Digest) :
    (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
      OracleComp HashSpec Digest).IsQueryBoundP p levels := by
  induction levels with
  | zero => simp [Concrete.authenticationRoot]
  | succ levels ih =>
      rw [Concrete.authenticationRoot]
      exact OracleComp.isQueryBoundP_bind ih fun _ _ =>
        authenticationNodeHash_isQueryBoundP_one p _ _ _ _ _

theorem verifyAfterLeaf_isQueryBoundP_treeHeight (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
      OracleComp HashSpec Bool).IsQueryBoundP p treeHeight := by
  unfold Concrete.verifyAfterLeaf
  generalize treeHeight = levels
  have hroot := authenticationRoot_isQueryBoundP_levels p publicKey.parameter leafIndex signature
    levels leaf
  have hbind := OracleComp.isQueryBoundP_bind (m := 0) hroot
    (ob := fun root => (pure (decide (root = publicKey.root)) : OracleComp HashSpec Bool))
    (fun _ _ => isQueryBoundP_pure _ _ _)
  rw [Nat.add_zero] at hbind
  exact hbind

end Generic

/-! ## The chain walks, for a predicate implying `IsDecidingInput` -/

section Deciding

variable (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
  (p : HashInput → Prop) [DecidablePred p]
  (hp : ∀ input, p input → IsDecidingInput parameter leafIndex chain input)

include hp

/-- The walk of chain `c` makes at most `chainLength - 1` deciding queries if `c` is the deciding
chain and none otherwise. -/
theorem recoverChain_isQueryBoundP_deciding (c : ChainIndex) (digit : Digit) (value : Digest) :
    (Concrete.recoverChain parameter leafIndex c digit value :
      OracleComp HashSpec Digest).IsQueryBoundP p (if c = chain then chainLength - 1 else 0) := by
  unfold Concrete.recoverChain
  by_cases hc : c = chain
  · rw [if_pos hc]
    exact (chainWalk_isQueryBoundP_steps p _ _ _ _ _ _).mono (Nat.sub_le _ _)
  · rw [if_neg hc]
    exact chainWalk_isQueryBoundP_zero p _ _ _ _ _ _ fun step value h =>
      not_isDecidingInput_chain_ne parameter leafIndex chain leafIndex c step _ hc (hp _ h)

theorem recoverEndpoints_isQueryBoundP_deciding (encoding : Encoding) (signature : Signature) :
    (Concrete.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP p (chainLength - 1) := by
  unfold Concrete.recoverEndpoints
  have hsum := Direct.sequenceFin_isQueryBoundP
    (fun c => (Concrete.recoverChain parameter leafIndex c (encoding c) (signature.chainValue c) :
      OracleComp HashSpec Digest))
    (fun c => if c = chain then chainLength - 1 else 0) p
    (fun c => recoverChain_isQueryBoundP_deciding parameter leafIndex chain p hp c _ _)
  simpa [Finset.sum_ite_eq'] using hsum

/-- One verification makes at most `decidingQueryBound = 40` queries satisfying a predicate that
implies `IsDecidingInput parameter leafIndex chain`, on every branch. -/
theorem verify_isQueryBoundP_of_imp_isDecidingInput (publicKey : PublicKey)
    (hparam : publicKey.parameter = parameter) (message : Message) (signature : Signature) :
    (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool).IsQueryBoundP
      p decidingQueryBound := by
  simp only [Concrete.verify_eq_decode]
  have hsplit : decidingQueryBound = 0 + ((chainLength - 1) + (1 + treeHeight)) := by
    unfold decidingQueryBound; omega
  rw [hsplit]
  refine OracleComp.isQueryBoundP_bind ?_ ?_
  · rw [Concrete.encodingHash]
    refine tweakableHash_isQueryBoundP_zero p _ _ _ fun h => ?_
    rw [hparam] at h
    exact not_isDecidingInput_encoding parameter leafIndex chain _ _ (hp _ h)
  intro digest _
  cases hdecode : Code.decodeDigest digest with
  | none => simp
  | some encoding =>
      simp only
      refine OracleComp.isQueryBoundP_bind ?_ fun endpoints _ =>
        OracleComp.isQueryBoundP_bind (tweakableHash_isQueryBoundP_one p _ _ _) fun leaf _ =>
          verifyAfterLeaf_isQueryBoundP_treeHeight p _ _ _ _
      rw [hparam]
      exact recoverEndpoints_isQueryBoundP_deciding parameter leafIndex chain p hp encoding
        signature

end Deciding

/-! ## The verifier -/

open Classical in
/-- One verification makes at most `decidingQueryBound = 40` hash queries whose input is moved by
`decidingTargetInput secretKey cache leafIndex chain`, on every branch. -/
theorem verify_isQueryBoundP_decidingTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (hparam : publicKey.parameter = secretKey.parameter) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (chain : ChainIndex) :
    (Concrete.verify publicKey leafIndex message signature : OracleComp HashSpec Bool).IsQueryBoundP
      (fun input => decidingTargetInput secretKey cache leafIndex chain input ≠ input)
      decidingQueryBound :=
  verify_isQueryBoundP_of_imp_isDecidingInput secretKey.parameter leafIndex chain
    (fun input => decidingTargetInput secretKey cache leafIndex chain input ≠ input)
    (fun input hne => isDecidingInput_of_decidingTargetInput_ne secretKey cache leafIndex chain
      input hne)
    publicKey hparam message signature

/-! ## The lifted verifier -/

/-- The scheme's verifier makes at most `decidingQueryBound` hash queries moved by
`decidingTargetInput`, on every branch. -/
theorem scheme_verify_isQueryBoundP_deciding (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (publicKey : PublicKey) (hparam : publicKey.parameter = secretKey.parameter)
    (leafIndex : LeafIndex) (message : Message) (signature : Signature) (chain : ChainIndex) :
    (Concrete.scheme.verify publicKey leafIndex message signature).IsQueryBoundP
      (Rom.IsRelevantHashQuery fun input =>
        decidingTargetInput secretKey cache leafIndex chain input ≠ input)
      decidingQueryBound := by
  classical
  change (liftComp (Concrete.verify publicKey leafIndex message signature :
    OracleComp HashSpec Bool) OracleWorld).IsQueryBoundP _ _
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (p := fun input => decidingTargetInput secretKey cache leafIndex chain input ≠ input)
    (fun _ => Iff.rfl)
    (verify_isQueryBoundP_decidingTargetInput secretKey cache publicKey hparam leafIndex message
      signature chain)

/-- From every starting cache, the expected number of the verifier's hash queries moved by
`decidingTargetInput` is at most `decidingQueryBound`. -/
theorem expectedSimulatedQueryCount_verify_deciding_le (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (hparam : publicKey.parameter = secretKey.parameter) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (chain : ChainIndex)
    (initialCache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        decidingTargetInput secretKey cache leafIndex chain input ≠ input)
      (Concrete.scheme.verify publicKey leafIndex message signature) initialCache ≤
      decidingQueryBound :=
  expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ initialCache decidingQueryBound
    (scheme_verify_isQueryBoundP_deciding secretKey cache publicKey hparam leafIndex message
      signature chain)

end XmssSecurity.Generic.Deciding

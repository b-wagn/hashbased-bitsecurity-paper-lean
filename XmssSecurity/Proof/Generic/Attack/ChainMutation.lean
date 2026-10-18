import XmssSecurity.Proof.Generic.CappedChain.SignatureChainValue
import XmssSecurity.Proof.Generic.Direct.Basic
import XmssSecurity.Proof.Generic.ExactQueryCount
import XmssSecurity.Proof.Common.QueryCounting

/-! The concrete one-request adversary for the 123-bit upper bound. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.Attack

variable [Code]

def mutationRequest : SignRequest := ⟨⟨0, by norm_num [lifetime]⟩, 0⟩

def fallbackSignature : Signature where
  randomness := 0
  chainValue := fun _ => 0
  authPath := fun _ => 0

/-- Only the chosen chain value changes; the request, randomizer, and authentication path stay
those of the requested signature. The fallback is used only when the signer returns `none`. -/
def chainMutationForgery (answer : Option Signature) (choice : ChainIndex × Digest) : Forgery :=
  ⟨mutationRequest.epoch, mutationRequest.message,
    CappedChain.replaceSignatureChainValue (answer.getD fallbackSignature) choice.1 choice.2⟩

local instance : Nonempty ChainIndex := ⟨⟨0, Code.numChains_pos⟩⟩

noncomputable local instance : SampleableType (ChainIndex × Digest) :=
  SampleableType.ofFintype (ChainIndex × Digest)

noncomputable def mutationChoice : ProbComp (ChainIndex × Digest) := $ᵗ (ChainIndex × Digest)

theorem mutationChoice_evalDist : evalDist mutationChoice =
    (liftM (PMF.uniformOfFintype (ChainIndex × Digest)) : SPMF (ChainIndex × Digest)) := by
  exact evalDist_uniformSample (ChainIndex × Digest)

attribute [irreducible] mutationChoice

def liftPrivateSamples {α : Type} (computation : ProbComp α) :
    OracleComp (OracleWorld + SigningSpec) α :=
  simulateQ (fun input => liftM ((OracleWorld + SigningSpec).query (.inl (.inl input)))) computation

noncomputable def chainMutationMain : OracleComp (OracleWorld + SigningSpec) Forgery := do
  let answer ← liftM ((OracleWorld + SigningSpec).query (.inr mutationRequest))
  let choice ← liftPrivateSamples mutationChoice
  return chainMutationForgery answer choice

noncomputable def chainMutationAdversary : Adversary := ⟨fun _ => chainMutationMain⟩

noncomputable def chainMutationSufCmaAdversary :
    SUFCMA.Adversary OracleWorld PublicKey Message Signature lifetime :=
  ⟨fun _ => chainMutationMain⟩

def IsHashOrRequest : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inl _) => False
  | _ => True

instance : DecidablePred IsHashOrRequest := fun input => by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash <;> unfold IsHashOrRequest <;> infer_instance
  · unfold IsHashOrRequest
    infer_instance

theorem liftPrivateSamples_zero {α : Type} (computation : ProbComp α)
    (predicate : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred predicate]
    (hfree : ∀ input, ¬predicate (.inl (.inl input))) :
    (liftPrivateSamples computation).IsQueryBoundP predicate 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftPrivateSamples]
  | query_bind input next ih =>
      unfold liftPrivateSamples at ih ⊢
      rw [simulateQ_bind, simulateQ_spec_query, OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (hfree input), fun answer => ?_⟩
      simpa only [if_neg (hfree input), Nat.sub_zero] using ih answer

private theorem mutationChoices_direct_zero :
    (liftPrivateSamples mutationChoice).IsQueryBoundP Direct.IsDirectHashQuery 0 :=
  liftPrivateSamples_zero _ _ Direct.not_isDirectHashQuery_uniform

private theorem mutationChoices_hashOrRequest_zero :
    (liftPrivateSamples mutationChoice).IsQueryBoundP IsHashOrRequest 0 :=
  liftPrivateSamples_zero _ _ (by intro input; simp [IsHashOrRequest])

theorem chainMutation_direct_zero : Direct.IsDirectQueryBound chainMutationAdversary 0 := by
  intro publicKey
  change chainMutationMain.IsQueryBoundP _ _
  unfold chainMutationMain
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (Direct.not_isDirectHashQuery_sign _), fun answer => ?_⟩
  simpa only [Direct.not_isDirectHashQuery_sign, if_false, Nat.sub_zero, bind_pure_comp,
    OracleComp.isQueryBoundP_map_iff] using mutationChoices_direct_zero

/-- Exactly one query is charged when both direct hashes and signing requests count. -/
theorem chainMutation_hashOrRequest_exact :
    ExactPredicateQueryCount IsHashOrRequest chainMutationMain 1 := by
  unfold chainMutationMain
  refine ExactPredicateQueryCount.query (spec := OracleWorld + SigningSpec)
    (predicate := IsHashOrRequest) (.inr mutationRequest) _ 0 ?_
  intro answer
  apply ExactQueryCount.ExactPredicateQueryCount.of_isQueryBoundP_zero
  rw [bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
  exact mutationChoices_hashOrRequest_zero

theorem chainMutationForgery_distinct_iff (signature : Signature) (choice : ChainIndex × Digest) :
    (chainMutationForgery (some signature) choice).signature ≠ signature ↔
      choice.2 ≠ signature.chainValue choice.1 := by
  constructor
  · contrapose!
    intro heq
    simp [chainMutationForgery, CappedChain.replaceSignatureChainValue, heq]
  · intro hvalue heq
    apply hvalue
    simpa [chainMutationForgery, CappedChain.replaceSignatureChainValue] using
      congrArg (fun sig => sig.chainValue choice.1) heq

theorem chainMutation_transcript_valid (answer : Option Signature) :
    SigningTranscript.Valid [⟨mutationRequest, answer⟩] := by
  simp [SUFCMA.SigningTranscript.Valid]

private theorem counted_eq_of_exact {ι α : Type} {spec : OracleSpec ι}
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    {computation : OracleComp spec α} {count : ℕ}
    (hexact : ExactPredicateQueryCount predicate computation count) :
    QueryCounting.counted predicate computation = (fun value => (value, count)) <$> computation := by
  induction hexact with
  | pure value => simp only [QueryCounting.counted_pure, map_pure]
  | query input next count hnext ih =>
      simp only [QueryCounting.counted_query_bind, ih, map_bind, bind_pure_comp,
        Functor.map_map, Nat.add_comm]

theorem chainMutation_counted :
    QueryCounting.counted IsHashOrRequest chainMutationMain =
      (fun forgery => (forgery, 1)) <$> chainMutationMain :=
  counted_eq_of_exact IsHashOrRequest chainMutation_hashOrRequest_exact

/-- info: 'XmssSecurity.Generic.Attack.chainMutation_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainMutation_counted

end XmssSecurity.Generic.Attack

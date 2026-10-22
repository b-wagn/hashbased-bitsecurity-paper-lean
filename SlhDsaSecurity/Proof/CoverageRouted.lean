import SlhDsaSecurity.Proof.CacheAvailability
import SlhDsaSecurity.Proof.SplitRouted

/-!
# The FORS branch's disclosed side, and the case it leaves open

`SplitRouted.signed_or_sensitive_of_secrets` sends each of the fourteen positions the forgery's
digest selects either to a sensitive claim or to membership of the disclosed set. This file
takes the second side to the event `CoverageTail` charges, and isolates exactly the case where
it cannot go there.

Membership of the disclosed set hands over a cached message-class input whose answer selects the
same position at the same FORS instance, and that is almost `CoverageTail.CoveredAt`. Three
reconciliations do the rest. A position determines the tree it sits in and the leaf inside it,
since the leaf is below `2 ^ forsHeight` and the position is `tree * 2 ^ forsHeight + leaf`, so a
witness at *some* tree is a witness at *that* tree. The FORS key a digest selects is its parsed
instance, repackaged. And two message inputs are equal only when their randomiser, key and
message all are.

**The case that is left over.** `CoveredAt` asks for witnesses *other than the forgery's own*
message input, and the disclosed set does not supply that: the forgery's own digest query, if
the signer's randomiser made it, is itself a disclosing entry and it selects its own positions.
So whenever the only witness is the forgery's own input, the coverage event does not fire.

Under strong freshness that case is reachable — a forgery may repeat a signed message with the
signer's randomiser and change the signature elsewhere — and it is charged structurally rather
than by coverage. The disclosed set being the signer's own digests is what makes it so: the
witness being the forgery's input forces the forgery's randomiser to be the signer's, which is
the hypothesis `CanonicalSignature.eq_signInternal` needs to identify the forgery with the
signature a request returned.

`forgeryDisclosedCovered_or_only_self` is therefore stated as a fork rather than an implication,
with the leftover case named rather than assumed away.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CoverageRouted

open Security CanonicalGraph

/-! ## A position names its tree and its leaf -/

/-- **A FORS position determines the tree it sits in and the leaf inside it.** -/
theorem forsIndex_inj {left right : SlhDsaSecurity.Fors.Indices}
    {treeLeft treeRight : Fin forsTrees}
    (hindex : GraphStakes.forsIndex left treeLeft = GraphStakes.forsIndex right treeRight) :
    treeLeft = treeRight ∧ left treeLeft = right treeRight := by
  have hval : treeLeft.val * 2 ^ forsHeight + (left treeLeft).val =
      treeRight.val * 2 ^ forsHeight + (right treeRight).val :=
    congrArg Fin.val hindex
  have hpow : (2 : Nat) ^ forsHeight = 4096 := by norm_num [forsHeight]
  have hvalues : treeLeft.val * 4096 + (left treeLeft).val =
      treeRight.val * 4096 + (right treeRight).val := by rw [← hpow]; exact hval
  have hleft : (left treeLeft).val < 4096 := by rw [← hpow]; exact (left treeLeft).isLt
  have hright : (right treeRight).val < 4096 := by rw [← hpow]; exact (right treeRight).isLt
  exact ⟨Fin.val_injective (by omega), Fin.val_injective (by omega)⟩

/-- **The FORS key a digest selects is its parsed instance.** -/
theorem parse_instance_eq_of_forsKeyOfDigest_eq {left right : HashOutput}
    (hkey : SplitCharged.forsKeyOfDigest left = SplitCharged.forsKeyOfDigest right) :
    (MessageDigest.parse left).1 = (MessageDigest.parse right).1 := by
  refine (CoverageTail.parse_instance_eq_iff left right).mpr ⟨?_, ?_⟩
  · exact BitVec.toFin_injective (congrArg ForsKey.tree hkey)
  · exact BitVec.toFin_injective (congrArg ForsKey.leaf hkey)

/-! ## Two message inputs that differ -/

/-- **A message input is determined by its randomiser, key and message**, so a witness naming a
different pair is a witness of its own. -/
theorem messageInput_ne (pk : PublicKey) (randomizer randomizer' : Digest)
    (message message' : Bytes)
    (hne : randomizer ≠ randomizer' ∨ message ≠ message') :
    Hashing.messageInput randomizer pk message ≠
      Hashing.messageInput randomizer' pk message' := by
  intro hequal
  obtain ⟨hrandomizer, -, hmessage⟩ := Hashing.messageInput_injective hequal
  rcases hne with hne | hne
  · exact hne hrandomizer
  · exact hne hmessage

/-! ## The coverage event -/

/-- **The forgery's digest is covered**, given a witness of its own for every tree. -/
theorem forgeryCovered_of_witnesses (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hwitness : ∀ tree : MessageDigest.ForsTree,
      ∃ (other : Bytes) (otherAnswer : HashOutput),
        other ≠ Hashing.messageInput parsed.randomizer pk message ∧
          CombinedCharge.IsMessageInput pk other ∧ result.2 other = some otherAnswer ∧
          SplitCharged.forsKeyOfDigest otherAnswer = SplitCharged.forsKeyOfDigest answer ∧
          MessageDigest.forsIndices otherAnswer tree = MessageDigest.forsIndices answer tree) :
    CoverageTail.ForgeryCovered pk result := by
  refine ⟨message, parsed, answer, hframe, hparsed, hentry, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hclass, hother, hkey, hleaf⟩ := hwitness tree
  exact ⟨other, otherAnswer, hne, hclass, hother,
    parse_instance_eq_of_forsKeyOfDigest_eq hkey, hleaf⟩

/-! ## Coverage by the digests that actually disclose

The witnesses this fork produces are not arbitrary message-class digests: each comes with
`CacheAvailability.SignerRandomised`, because the disclosed set is defined by it. Keeping that
is what lets the coverage charge count the signer's own digests rather than every cached
`H_msg` answer — and the signer's are capped by the signing limit while the others are not.

The narrow event implies the wide one, so a charge stated against either applies. -/

/-- The digest `answer` has each of its fourteen FORS leaves also selected, at the same FORS
instance, by the digest cached at some *disclosing* input other than the target. -/
def DisclosedCoveredAt (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (target : Bytes) (answer : HashOutput) : Prop :=
  ∀ tree : MessageDigest.ForsTree, ∃ (other : Bytes) (otherAnswer : HashOutput),
    other ≠ target ∧ CacheAvailability.SignerRandomised prfSeed pk cache other ∧
      cache other = some otherAnswer ∧
      (MessageDigest.parse otherAnswer).1 = (MessageDigest.parse answer).1 ∧
      (MessageDigest.parse otherAnswer).2 tree = (MessageDigest.parse answer).2 tree

/-- **The coverage event at the forgery's own digest, counted on the disclosing class.** -/
def ForgeryDisclosedCovered (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) : Prop :=
  ∃ (message : Bytes) (parsed : Signature) (answer : HashOutput),
    result.1.1.forgery.message.frame = some message ∧
      Signature.fromBytes? result.1.1.forgery.signature = some parsed ∧
        result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer ∧
          DisclosedCoveredAt prfSeed pk result.2
            (Hashing.messageInput parsed.randomizer pk message) answer

/-- **A disclosing witness is a message-class witness**, so the narrow coverage event is a case
of the wide one. -/
theorem forgeryCovered_of_disclosed (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec)
    (hcovered : ForgeryDisclosedCovered prfSeed pk result) :
    CoverageTail.ForgeryCovered pk result := by
  obtain ⟨message, parsed, answer, hframe, hparsed, hentry, hcovered⟩ := hcovered
  refine ⟨message, parsed, answer, hframe, hparsed, hentry, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hsigner, hother, hinstance, hleaf⟩ := hcovered tree
  exact ⟨other, otherAnswer, hne,
    CacheAvailability.isMessageInput_of_signerRandomised prfSeed pk result.2 other hsigner,
    hother, hinstance, hleaf⟩

/-- **The forgery's digest is covered by disclosing digests**, given a disclosing witness of its
own for every tree. -/
theorem forgeryDisclosedCovered_of_witnesses (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hwitness : ∀ tree : MessageDigest.ForsTree,
      ∃ (other : Bytes) (otherAnswer : HashOutput),
        other ≠ Hashing.messageInput parsed.randomizer pk message ∧
          CacheAvailability.SignerRandomised prfSeed pk result.2 other ∧
          result.2 other = some otherAnswer ∧
          SplitCharged.forsKeyOfDigest otherAnswer = SplitCharged.forsKeyOfDigest answer ∧
          MessageDigest.forsIndices otherAnswer tree = MessageDigest.forsIndices answer tree) :
    ForgeryDisclosedCovered prfSeed pk result := by
  refine ⟨message, parsed, answer, hframe, hparsed, hentry, fun tree => ?_⟩
  obtain ⟨other, otherAnswer, hne, hsigner, hother, hkey, hleaf⟩ := hwitness tree
  exact ⟨other, otherAnswer, hne, hsigner, hother,
    parse_instance_eq_of_forsKeyOfDigest_eq hkey, hleaf⟩

/-- **The disclosed side goes to coverage, or the forgery is its own only witness.** The second
case is the one strong freshness permits: a forgery that repeats a signed message with the
signer's own randomiser shares its message input with the signature that disclosed the secrets,
and then there is no other input to cover it. -/
theorem forgeryDisclosedCovered_or_only_self (prfSeed : Digest) (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hsigned : ∀ tree : MessageDigest.ForsTree,
      GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree ∈
        CacheAvailability.signedAt prfSeed pk result.2 (SplitCharged.forsKeyOfDigest answer)) :
    ForgeryDisclosedCovered prfSeed pk result ∨
      ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
        CacheAvailability.SignerRandomised prfSeed pk result.2 input → result.2 input = some a →
          SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
            (∃ other : MessageDigest.ForsTree,
              GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
                GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
              input = Hashing.messageInput parsed.randomizer pk message := by
  classical
  by_cases hself : ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
      CacheAvailability.SignerRandomised prfSeed pk result.2 input → result.2 input = some a →
        SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
          (∃ other : MessageDigest.ForsTree,
            GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
              GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
            input = Hashing.messageInput parsed.randomizer pk message
  · exact Or.inr hself
  refine Or.inl (forgeryDisclosedCovered_of_witnesses prfSeed pk result message parsed answer
    hframe hparsed hentry fun tree => ?_)
  push Not at hself
  obtain ⟨input, a, hsigner, hcached, hkey, ⟨other, hother⟩, hne⟩ := hself tree
  obtain ⟨htree, hleaf⟩ := forsIndex_inj hother
  exact ⟨input, a, hne, hsigner, hcached, hkey, htree ▸ hleaf⟩

end SlhDsaSecurity.CoverageRouted

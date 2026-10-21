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

**What is left open, and it is a real case.** `CoveredAt` asks for witnesses *other than the
forgery's own* message input. The disclosed set does not supply that: the forgery's own digest
query is itself a cached message-class entry, and it selects its own positions. So whenever the
only witness is the forgery's own input, the coverage event does not fire.

That is not an artefact. Under strong freshness a forgery may repeat a message that was signed,
reusing the signer's own randomiser, and change the signature elsewhere; then the forgery's
message input *is* the signer's, one cached entry accounts for all fourteen positions, and no
other message input need exist. The forgery is a win, the FORS secrets it opens are honestly
held, and nothing about them is rare. Such a win has to be charged on the structural side — the
rest of the signature must differ, and a different signature reaching the same root is a
collision or a fault — and `WarmedSplit.cases_of_win` does not currently keep that information
in this branch, because the recovered FORS key being genuine satisfies its left disjunct
outright.

`forgeryCovered_or_only_self` is therefore stated as a fork rather than an implication, with the
open case named rather than assumed away.
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

/-- **The disclosed side goes to coverage, or the forgery is its own only witness.** The second
case is the one strong freshness permits: a forgery that repeats a signed message with the
signer's own randomiser shares its message input with the signature that disclosed the secrets,
and then there is no other input to cover it. -/
theorem forgeryCovered_or_only_self (pk : PublicKey)
    (result : (Outcome × Nat) × QueryCache HashSpec) (message : Bytes) (parsed : Signature)
    (answer : HashOutput)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hentry : result.2 (Hashing.messageInput parsed.randomizer pk message) = some answer)
    (hsigned : ∀ tree : MessageDigest.ForsTree,
      GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree ∈
        CacheAvailability.signedAt pk result.2 (SplitCharged.forsKeyOfDigest answer)) :
    CoverageTail.ForgeryCovered pk result ∨
      ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
        CombinedCharge.IsMessageInput pk input → result.2 input = some a →
          SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
            (∃ other : MessageDigest.ForsTree,
              GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
                GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
              input = Hashing.messageInput parsed.randomizer pk message := by
  classical
  by_cases hself : ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (a : HashOutput),
      CombinedCharge.IsMessageInput pk input → result.2 input = some a →
        SplitCharged.forsKeyOfDigest a = SplitCharged.forsKeyOfDigest answer →
          (∃ other : MessageDigest.ForsTree,
            GraphStakes.forsIndex (MessageDigest.forsIndices a) other =
              GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree) →
            input = Hashing.messageInput parsed.randomizer pk message
  · exact Or.inr hself
  refine Or.inl (forgeryCovered_of_witnesses pk result message parsed answer hframe hparsed
    hentry fun tree => ?_)
  push Not at hself
  obtain ⟨input, a, hclass, hcached, hkey, ⟨other, hother⟩, hne⟩ := hself tree
  obtain ⟨htree, hleaf⟩ := forsIndex_inj hother
  exact ⟨input, a, hne, hclass, hcached, hkey, htree ▸ hleaf⟩

end SlhDsaSecurity.CoverageRouted

import SlhDsaSecurity.Proof.CanonicalGraph.Input
import SlhDsaSecurity.Proof.HashSeparation

/-! Every canonical structural coordinate fits the existing shared-input separation bound. -/

namespace SlhDsaSecurity.CanonicalGraph

private theorem zero32 : BitVec.toNat (0 : BitVec 32) = 0 := rfl

theorem StructuralNode.address_withinBounds (node : StructuralNode) :
    HashSeparation.WithinBounds node.address := by
  cases node with
  | tree tree height index =>
      have hi := index.isLt.trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le subtreeHeight (height.val + 1)))
      norm_num [HashSeparation.WithinBounds, StructuralNode.address, Tree.address,
        Merkle.nodeAddress, Hypertree.address, Address.setTypeAndClear, zero32,
        subtreeHeight, layers, totalHeight] at *
      simp only [subtreeHeight, layers, totalHeight] at *
      omega
  | forsTree key height index =>
      have hi := index.isLt.trans_le (Nat.mul_le_mul_left forsTrees
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le forsHeight height.val)))
      norm_num [HashSeparation.WithinBounds, StructuralNode.address, ForsKey.address,
        Fors.nodeAddress, Hypertree.address, Address.setTypeAndClear, zero32,
        subtreeHeight, totalHeight, forsHeight, forsTrees] at *
      simp only [subtreeHeight, totalHeight, forsHeight, forsTrees] at *
      omega
  | _ =>
      norm_num [HashSeparation.WithinBounds, StructuralNode.address, WotsKey.address,
        Tree.address, ForsKey.address, Wots.secretAddress, Wots.publicKeyAddress,
        Merkle.wotsAddress, Fors.secretAddress, Hypertree.address,
        Address.setTypeAndClear, zero32, subtreeHeight, layers, totalHeight,
        forsHeight, forsTrees, chains, messageDigits, checksumDigits, n, winternitzBits, w] at *
      simp only [subtreeHeight, layers, totalHeight, forsHeight, forsTrees,
        chains, messageDigits, checksumDigits, n, winternitzBits, w] at *
      omega

theorem message_canonical_ne {randomizer publicSeed : Digest} {pk : PublicKey}
    {message : Bytes} {cells : Cells} {parent : StructuralNode}
    (hpublic : ¬ HashSeparation.Possible (pk.seed, pk.root)) :
    Hashing.messageInput randomizer pk message ≠ canonicalInput publicSeed cells parent :=
  HashSeparation.message_tweakable_ne hpublic parent.address_withinBounds

end SlhDsaSecurity.CanonicalGraph

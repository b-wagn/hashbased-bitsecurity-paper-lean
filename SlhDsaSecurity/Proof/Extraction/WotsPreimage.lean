import SlhDsaSecurity.Proof.Extraction.Wots
import SlhDsaSecurity.Proof.ChecksumAntichain

/-! The WOTS one-wayness witness for a hypertree layer transition.

When a layer's canonical branch forces `sig.wots = Wots.sign forged` for a message
`forged` that differs from the honestly signed message `signed` at the same WOTS key,
the checksum antichain yields a chain where the forged value is a strict chain-ancestor
of the honestly revealed value: advancing the forged value reaches the honest one. This
is a pure chain-arithmetic witness, feeding the ROM preimage probability charge. No
one-wayness is assumed here. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.WotsPreimage

variable [HasQuery HashSpec Id]

/-- The chain-step address of chain `i` for this WOTS key. -/
def chainAddress (address : Address) (i : Fin chains) : Address :=
  { address with chainOrHeight := BitVec.ofNat 32 i.val }

/-- Advancing a chain from position `a` to position `b` composes the two segments. -/
theorem chain_le (publicSeed : Digest) (address : Address) (a b : Nat) (hab : a ≤ b)
    (value : Digest) :
    SlhDsaSecurity.Wots.chain (m := Id) publicSeed address a (b - a)
        (SlhDsaSecurity.Wots.chain (m := Id) publicSeed address 0 a value) =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed address 0 b value := by
  conv_rhs => rw [show b = a + (b - a) from by omega]
  rw [Correctness.Wots.chain_add publicSeed address 0 a (b - a) value, Nat.zero_add]

/-- Each honest WOTS signature value is the chain started from the derived secret,
advanced to the message digit. -/
theorem sign_eq_chain (message secretSeed publicSeed : Digest) (address : Address) (i : Fin chains) :
    SlhDsaSecurity.Wots.sign (m := Id) message secretSeed publicSeed address i =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed (chainAddress address i)
        0 (Checksum.encode message i).val
        (Hashing.derive (m := Id) publicSeed secretSeed
          (SlhDsaSecurity.Wots.secretAddress address i)) := by
  simp only [SlhDsaSecurity.Wots.sign, Correctness.sequenceFin_id, bind, chainAddress]

/-- On any chain where the forged digit is strictly smaller, the forged WOTS value is a
strict chain-ancestor of the honestly revealed value: advancing it by the digit gap
reaches the honest signature value. -/
theorem forged_advances_to_signed (signed forged secretSeed publicSeed : Digest)
    (address : Address) (i : Fin chains)
    (hlt : (Checksum.encode forged i).val < (Checksum.encode signed i).val) :
    SlhDsaSecurity.Wots.chain (m := Id) publicSeed (chainAddress address i)
        (Checksum.encode forged i).val
        ((Checksum.encode signed i).val - (Checksum.encode forged i).val)
        (SlhDsaSecurity.Wots.sign (m := Id) forged secretSeed publicSeed address i) =
      SlhDsaSecurity.Wots.sign (m := Id) signed secretSeed publicSeed address i := by
  rw [sign_eq_chain, sign_eq_chain]
  exact chain_le publicSeed (chainAddress address i) (Checksum.encode forged i).val
    (Checksum.encode signed i).val (Nat.le_of_lt hlt) _

/-- A forged WOTS signature matching the canonical signature of a different message
exhibits a concrete chain on which the forged value is a strict preimage-chain-ancestor
of the honestly revealed value. This is the WOTS one-wayness witness; its probability is
charged separately in the ROM. -/
theorem exists_preimage_witness (signed forged secretSeed publicSeed : Digest)
    (address : Address) (hne : signed ≠ forged) :
    ∃ i : Fin chains, (Checksum.encode forged i).val < (Checksum.encode signed i).val ∧
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed (chainAddress address i)
        (Checksum.encode forged i).val
        ((Checksum.encode signed i).val - (Checksum.encode forged i).val)
        (SlhDsaSecurity.Wots.sign (m := Id) forged secretSeed publicSeed address i) =
      SlhDsaSecurity.Wots.sign (m := Id) signed secretSeed publicSeed address i := by
  obtain ⟨i, hi⟩ := Checksum.exists_decreased_digit hne
  have hlt : (Checksum.encode forged i).val < (Checksum.encode signed i).val := hi
  exact ⟨i, hlt, forged_advances_to_signed signed forged secretSeed publicSeed address i hlt⟩

end SlhDsaSecurity.Extraction.WotsPreimage

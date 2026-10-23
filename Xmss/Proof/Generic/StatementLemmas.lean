import Xmss.Proof.Generic.IdealStatement
import Xmss.Proof.Generic.Wots
import Xmss.Proof.Generic.Code

/-!
Proof-side mirrors of the sealed statement definitions, and rewrite lemmas restating them so proofs can unfold them without unsealing.

The statement materializes the secret key's vectors from `evalWithAnswerFn (replayHash cache)`
during key generation. `Wots.walk`, `CacheView`, and `CacheReplay` describe the same stored values
as functions for the proofs; `Proof.CacheReplayEval` proves that vector lookups agree with them.
-/

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

open Hashing Wots Merkle Verify Keygen Signing

namespace CacheView

def digestAt (cache : QueryCache HashSpec) (input : HashInput) : Digest :=
  match cache input with
  | some output => output
  | none => 0

def tweakableHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (domain : HashDomain) (payload : HashInput) : Digest :=
  digestAt cache (Xmss.Generic.tweakableHashInput parameter domain payload)

def encodingInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness) : HashInput :=
  Xmss.Generic.tweakableHashInput parameter (.encoding leafIndex)
    (Hashing.encodingPayload input.1 input.2)

def chainInput (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position : ChainStep) (value : Digest) : HashInput :=
  Xmss.Generic.tweakableHashInput parameter (.chain leafIndex chain position)
    (Hashing.digestBytes value)

def leafInput (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : HashInput :=
  Xmss.Generic.tweakableHashInput parameter (.leaf leafIndex)
    (Hashing.leafPayload endpoints)

def merkleInput (parameter : PublicParameter) (level : MerkleLevel)
    (node : MerkleNode) (left right : Digest) : HashInput :=
  Xmss.Generic.tweakableHashInput parameter (.merkle level node)
    (Hashing.nodePayload left right)

def encodingHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (input : Message × Randomness) : Digest :=
  digestAt cache (encodingInput parameter leafIndex input)

/-- The encoding of a recorded encoding query, and `none` for an unrecorded input: a decoded
encoding read from the cache witnesses that the query was made. -/
def decodedEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (input : Message × Randomness) : Option Encoding :=
  match cache (encodingInput parameter leafIndex input) with
  | some output => Code.decodeDigest (output)
  | none => none

theorem encodingInput_cached_of_decode_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : decodedEncoding cache parameter leafIndex (message, randomness) = some encoding) :
    ∃ output, cache (encodingInput parameter leafIndex (message, randomness)) = some output := by
  unfold decodedEncoding at hdecode
  split at hdecode
  · exact ⟨_, by assumption⟩
  · cases hdecode

theorem decodedEncoding_eq_of_cache_eq_some {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    {output : Digest} (hcache : cache (encodingInput parameter leafIndex input) = some output) :
    decodedEncoding cache parameter leafIndex input =
      Code.decodeDigest (encodingHash cache parameter leafIndex input) := by
  simp [decodedEncoding, encodingHash, digestAt, hcache]

theorem decodedEncoding_eq_of_input_eq {left right : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    (h : left (encodingInput parameter leafIndex input) =
      right (encodingInput parameter leafIndex input)) :
    decodedEncoding left parameter leafIndex input =
      decodedEncoding right parameter leafIndex input := by
  simp only [decodedEncoding, h]

theorem decodedEncoding_eq_of_cached {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    (hcache : ∃ output, cache (encodingInput parameter leafIndex input) = some output) :
    decodedEncoding cache parameter leafIndex input =
      Code.decodeDigest (encodingHash cache parameter leafIndex input) := by
  obtain ⟨output, houtput⟩ := hcache
  exact decodedEncoding_eq_of_cache_eq_some houtput

theorem decodeDigest_of_decodedEncoding {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    {encoding : Encoding} (hdecode : decodedEncoding cache parameter leafIndex input = some encoding) :
    Code.decodeDigest (encodingHash cache parameter leafIndex input) = some encoding := by
  rcases input with ⟨message, randomness⟩
  rw [← decodedEncoding_eq_of_cached (encodingInput_cached_of_decode_some cache parameter leafIndex
    message randomness encoding hdecode)]
  exact hdecode

theorem decodedEncoding_valid {cache : QueryCache HashSpec}
    {parameter : PublicParameter} {leafIndex : LeafIndex} {input : Message × Randomness}
    {encoding : Encoding} (hdecode : decodedEncoding cache parameter leafIndex input = some encoding) :
    Code.Valid encoding :=
  Code.decodeDigest_valid (decodeDigest_of_decodedEncoding hdecode)

def chainStep (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position : Nat) (value : Digest) : Digest :=
  if hposition : position < chainLength - 1 then
    digestAt cache (chainInput parameter leafIndex chain ⟨position, hposition⟩ value)
  else
    0

def leafHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) : Digest :=
  digestAt cache (leafInput parameter leafIndex endpoints)

def merkleHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) : Digest :=
  digestAt cache (merkleInput parameter level node left right)

abbrev nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  Merkle.nodeIndex leafIndex level

def authenticationNodePayload (leafIndex : LeafIndex) (level : Nat)
    (current sibling : Digest) : HashInput :=
  if leafIndex.val.testBit level then
    Hashing.nodePayload sibling current
  else
    Hashing.nodePayload current sibling

def nodeInput (parameter : PublicParameter) (leafIndex : LeafIndex) (level : MerkleLevel)
    (current sibling : Digest) : HashInput :=
  Xmss.Generic.tweakableHashInput parameter (.merkle level (nodeIndex leafIndex level.val))
    (authenticationNodePayload leafIndex level.val current sibling)

def nodeHash (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (left right : Digest) : Digest :=
  if hlevel : level < treeHeight then
    digestAt cache (nodeInput parameter leafIndex ⟨level, hlevel⟩ left right)
  else
    0

end CacheView

namespace CacheReplay

def oneTimePublicKey (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : ChainIndex → Digest :=
  fun chain => Wots.walk (CacheView.chainStep cache parameter leafIndex chain) 0
    (chainLength - 1) (secret leafIndex chain)

def leafAt (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (leafIndex : LeafIndex) : Digest :=
  CacheView.leafHash cache parameter leafIndex
    (oneTimePublicKey cache parameter secret leafIndex)

def treeNode (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → MerkleNode → Digest
  | 0, node => leafAt cache parameter secret node
  | levels + 1, node =>
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Merkle.childNode node false))
          (treeNode cache parameter secret levels (Merkle.childNode node true))
      else
        0

attribute [irreducible] treeNode

end CacheReplay

attribute [local semireducible] treeNode CacheReplay.treeNode sampleSecret signingRandomness

noncomputable local instance : SampleableType (LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (LeafIndex → ChainIndex → Digest)

@[simp]
theorem Merkle.treeNode_zero_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (node : MerkleNode) :
    treeNode (m := m) parameter secret 0 node =
      leafAt (m := m) parameter secret node := rfl

theorem Merkle.treeNode_succ_eq {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    treeNode (m := m) parameter secret (levels + 1) node = (do
      let left ← treeNode (m := m) parameter secret levels (childNode node false)
      let right ← treeNode (m := m) parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash (m := m) parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0) := rfl

theorem Keygen.sampleSecret_eq : sampleSecret = $ᵗ (LeafIndex → ChainIndex → Digest) := rfl

omit [Code] in
theorem Signing.signingRandomness_eq : signingRandomness = $ᵗ Randomness := rfl

namespace CacheReplay

@[simp]
theorem treeNode_zero_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (node : MerkleNode) :
    treeNode cache parameter secret 0 node = leafAt cache parameter secret node := by
  with_unfolding_all rfl

theorem treeNode_succ_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    treeNode cache parameter secret (levels + 1) node =
      if hlevel : levels < treeHeight then
        CacheView.merkleHash cache parameter ⟨levels, hlevel⟩ node
          (treeNode cache parameter secret levels (Merkle.childNode node false))
          (treeNode cache parameter secret levels (Merkle.childNode node true))
      else
        0 := by
  with_unfolding_all rfl

end CacheReplay

end Xmss.Generic

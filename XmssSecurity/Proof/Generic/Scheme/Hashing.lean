import XmssSecurity.Proof.Generic.Scheme.Types

/-!
# XMSS hashing (proof copy)

The proofs work with this copy of the hash routines of the statement, for the code `Code`;
`Bridge.lean` proves that it computes the statement's algorithms.

How XMSS calls the hash function: the serialization of hash inputs (little-endian byte strings
and the 9-byte tweaks `enc(t, p, j)`), the hash domains, and the hash routines built on a
single oracle query `oracleHash`: the tweakable hash `Th` and its uses for the message encoding,
chain steps, leaves, and Merkle nodes, and the derivation of keys and randomizers from the master
seed. The hash routines work in any monad with access to `HashSpec`.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Generic

variable [Code]

/-! ## Hash inputs and tweaks -/

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The fields of a tweak `enc(t, p, j)`: a one-byte type `t` and two 32-bit integers `p`, `j`. -/
structure TweakFields where
  tag : BitVec 8
  position : BitVec 32
  leafIndex : BitVec 32
deriving DecidableEq

/-- The 9 tweak bytes `enc(t, p, j) = t || LE32(p) || LE32(j)`.
The one-byte tag separates the hash domains; there is no padding. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  bytesLE 1 fields.tag ++ bytesLE 4 fields.position ++ bytesLE 4 fields.leafIndex

/-- Convert the three integer fields to their fixed widths. -/
def tweakFields (tag position leafIndex : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 32 position, BitVec.ofNat 32 leafIndex⟩

/-- The verification hash domains, tweak types `1` to `4`. -/
inductive HashDomain where
  | chain (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
  | leaf (leafIndex : LeafIndex)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (leafIndex : LeafIndex)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain leafIndex chain step => tweakFields 1 (chainLength * chain + step) leafIndex
  | .leaf leafIndex => tweakFields 2 0 leafIndex
  | .merkle level node => tweakFields 3 (level.val + 1) node
  | .encoding leafIndex => tweakFields 4 0 leafIndex

/-- The 9 tweak bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-- `tweak(7, trial, leafIndex) || P || S || m`. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) (trial : BitVec 32) : HashInput :=
  fieldBytes ⟨7#8, trial, BitVec.ofNat 32 leafIndex.val⟩ ++
    bytesLE 16 parameter ++ bytesLE 32 seed ++ bytesLE 32 message

inductive KeygenDomain where
  | parameter
  | chain (leafIndex : LeafIndex) (chain : ChainIndex)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0
  | .chain leafIndex chain => tweakFields 0 chain leafIndex

/-- `tweak || P || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

/-! ## Hash routines -/

namespace Concrete

/-- `m || rho`. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m Digest :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = H(tw || P || M)`. -/
def tweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest :=
  oracleHash (tweakableHashInput parameter domain payload)

/-- The message digest `D = Th(P, enc(4, 0, idx), m || rho)`. -/
def encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding leafIndex) (encodingPayload message randomness)

/-- One chain step, from position `step` to `step + 1`, under `enc(1, 2^w i + step, idx)`. -/
def chainHash (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain leafIndex chain step) (bytesLE 16 value)

/-- `X_{0,idx}`, the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf leafIndex) (leafPayload endpoints)

/-- `X_{level+1,node}` from its two children. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

def deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) : m Randomness :=
  Concrete.oracleHash (randomizerHashInput parameter seed leafIndex message trial)

end XmssSecurity.Generic

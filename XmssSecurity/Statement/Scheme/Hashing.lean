import XmssSecurity.Statement.Scheme.Types

/-!
# XMSS hashing

How XMSS calls the hash function: the serialization of hash inputs (little-endian byte strings
and the 16-byte tweaks `enc(t, p, j)`), the hash domains, and the hash routines built on a
single oracle query `oracleHash`: the tweakable hash `Th` and its uses for the message encoding,
chain steps, leaves, and Merkle nodes, and the derivation of keys and randomizers from the master
seed. The hash routines work in any monad with access to `HashSpec`.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-! ## Hash inputs and tweaks -/

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

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

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 0

/-- The 16 tweak bytes `enc(t, p, j) = protocol_domain_sep || t || 0^16 || p || 0^32 || j`, each
field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ [0, 0] ++ bytesLE 4 fields.position ++
    List.replicate 4 0 ++ bytesLE 4 fields.leafIndex

/-- Convert the three integer fields to their fixed widths. -/
def tweakFields (tag position leafIndex : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 32 position, BitVec.ofNat 32 leafIndex⟩

/-- The verification hash domains, tweak types `1` to `4`. A chain step names its chain by its
index `i`. -/
inductive HashDomain where
  | chain (leafIndex : LeafIndex) (chain : Nat) (step : ChainStep)
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

/-- The 16 tweak bytes of a hash domain. -/
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

/-- The key-derivation domains: the public parameter, and the start of chain `i` of a leaf. -/
inductive KeygenDomain where
  | parameter
  | chain (leafIndex : LeafIndex) (chain : Nat)
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

/-- `m || rho || 0^128`. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness ++ List.replicate 16 0

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload {v : Nat} (endpoints : Fin v → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-- The message digest `D = Th(P, enc(4, 0, idx), m || rho || 0^128)`, which the WOTS encoding
decodes. -/
def encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding leafIndex) (encodingPayload message randomness)

/-- One chain step, from position `step` to `step + 1`, under `enc(1, 2^w i + step, idx)`. -/
def chainHash {v : Nat} (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : Fin v)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain leafIndex chain.val step) (bytesLE 16 value)

/-- `X_{0,idx}`, the hash of the `v` public values. -/
def leafHash {v : Nat} (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : Fin v → Digest) : m Digest :=
  tweakableHash parameter (.leaf leafIndex) (leafPayload endpoints)

/-- `X_{level+1,node}` from its two children. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `Th(P, enc, S)`: the public parameter (`P = 0`, `enc(5, 0, 0)`) and the chain starts
(`enc(0, i, idx)`). -/
def deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- Randomizer trial `a`: `ρ_a = Truncate_ℓrnd(H(enc(7, a, idx) ∥ P ∥ S ∥ m))`. -/
def deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return (← Concrete.oracleHash (randomizerHashInput parameter seed leafIndex message trial)).extractLsb' 0 randomnessBits

end XmssSecurity

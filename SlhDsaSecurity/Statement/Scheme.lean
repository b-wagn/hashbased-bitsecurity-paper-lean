import SlhDsaSecurity.Statement.Fors
import SlhDsaSecurity.Statement.Hypertree

/-!
# Deterministic pure SLH-DSA-128s

FIPS 205 Algorithms 18–22 and 24, using the single ideal hash in `Hashing` with
the standard SHAKE input formats. These are concrete algorithms, not a claim
about the security of SHAKE256. Secret leaves are derived only when needed.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Scheme

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Algorithm 18 computes only the top height-nine XMSS tree. -/
def keygenInternal (secretSeed prfSeed publicSeed : Digest) : m (SecretKey × PublicKey) := do
  let root ← Merkle.node secretSeed publicSeed (Hypertree.address (layers - 1) 0)
    subtreeHeight 0
  let pk : PublicKey := { seed := publicSeed, root }
  return ({ seed := secretSeed, prf := prfSeed, publicKey := pk }, pk)

/-- Algorithm 21 with three independent uniform 16-byte seeds. Sampling cannot fail in this model. -/
noncomputable def keygen [HasQuery unifSpec m] : m (SecretKey × PublicKey) := do
  let secretSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let prfSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  let publicSeed ← simulateQ (fun i => query (spec := unifSpec) i) ($ᵗ Digest)
  keygenInternal secretSeed prfSeed publicSeed

def forsAddress (digest : HashOutput) : Address :=
  { (Hypertree.address 0 (MessageDigest.treeIndex digest).toNat).setTypeAndClear .forsTree with
    keyPair := BitVec.ofNat 32 (MessageDigest.leafIndex digest).toNat }

/-- Algorithm 19, with deterministic opt_rand = PK.seed. -/
def signInternal (sk : SecretKey) (message : Bytes) : m Signature := do
  let randomizer ← Hashing.randomizer sk.prf sk.publicKey.seed message
  let digest ← Hashing.messageDigest randomizer sk.publicKey message
  let indices := MessageDigest.forsIndices digest
  let address := forsAddress digest
  let fors ← Fors.sign indices sk.seed sk.publicKey.seed address
  let forsKey ← Fors.publicKeyFromSignature fors indices sk.publicKey.seed address
  let hypertree ← Hypertree.sign forsKey sk.seed sk.publicKey.seed
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin
  return { randomizer, fors, hypertree }

/-- Algorithm 20 after the fixed-width signature has been parsed. -/
def verifyInternal (pk : PublicKey) (message : Bytes) (signature : Signature) : m Bool := do
  let digest ← Hashing.messageDigest signature.randomizer pk message
  let forsKey ← Fors.publicKeyFromSignature signature.fors (MessageDigest.forsIndices digest)
    pk.seed (forsAddress digest)
  Hypertree.verify forsKey signature.hypertree pk
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin

/-- Algorithm 22, including rejection of contexts longer than 255 bytes. -/
def sign (sk : SecretKey) (request : Message) : m (Option Bytes) := do
  match request.frame with
  | none => return none
  | some message => return some (← signInternal sk message).toBytes

/-- Algorithm 24. Invalid context or signature length causes rejection with no hash calls. -/
def verify (pk : PublicKey) (request : Message) (signature : Bytes) : m Bool := do
  match request.frame with
  | none => return false
  | some message =>
    match Signature.fromBytes? signature with
    | none => return false
    | some parsed => verifyInternal pk message parsed

end SlhDsaSecurity.Scheme

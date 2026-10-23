import «SLH-DSA-128s».Statement.Types

/-!
# Standard SLH-DSA-128s signature layout

The structured representation follows FIPS 205 Figures 10, 11, 14, and 17.
`Signature.toBytes` and `Signature.fromBytes?` use the standard 7856-byte layout;
the byte-facing verifier rejects every other length before querying the oracle.
-/

namespace SlhDsaSecurity

abbrev WotsSignature := Fin chains → Digest

structure XmssSignature where
  wots : WotsSignature
  authentication : Fin subtreeHeight → Digest
deriving DecidableEq

structure ForsTreeSignature where
  secret : Digest
  authentication : Fin forsHeight → Digest
deriving DecidableEq

abbrev ForsSignature := Fin forsTrees → ForsTreeSignature
abbrev HypertreeSignature := Fin layers → XmssSignature

structure Signature where
  randomizer : Digest
  fors : ForsSignature
  hypertree : HypertreeSignature
deriving DecidableEq

/-- Run the indexed computations in increasing order, retaining all oracle calls. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} :
    (size : Nat) → (Fin size → m α) → m (Fin size → α)
  | 0, _ => pure Fin.elim0
  | size + 1, f => do
    let first ← f 0
    let rest ← sequenceFin size (fun i => f i.succ)
    return Fin.cases first rest

/-- Concatenate fixed-width digest fields in increasing index order. -/
def digestArrayBytes {size : Nat} (values : Fin size → Digest) : Bytes :=
  (List.ofFn fun i => bytesBE n (values i)).flatten

def XmssSignature.toBytes (signature : XmssSignature) : Bytes :=
  digestArrayBytes signature.wots ++ digestArrayBytes signature.authentication

def ForsTreeSignature.toBytes (signature : ForsTreeSignature) : Bytes :=
  bytesBE n signature.secret ++ digestArrayBytes signature.authentication

def Signature.toBytes (signature : Signature) : Bytes :=
  bytesBE n signature.randomizer ++
    (List.ofFn fun i => (signature.fors i).toBytes).flatten ++
    (List.ofFn fun i => (signature.hypertree i).toBytes).flatten

/-- Read one 16-byte big-endian field at a byte offset. The enclosing decoder checks length. -/
def Signature.readDigest (input : Bytes) (offset : Nat) : Digest :=
  ((input.drop offset).take n).foldl
    (fun value byte => (value <<< 8) ||| BitVec.ofNat (8 * n) byte.toNat) 0

/-- Parse the standard fixed-width layout; no noncanonical or trailing bytes are accepted. -/
def Signature.fromBytes? (input : Bytes) : Option Signature :=
  if input.length = signatureBytes then
    some {
      randomizer := readDigest input 0
      fors := fun i => {
        secret := readDigest input (n * (1 + i.val * (1 + forsHeight)))
        authentication := fun j =>
          readDigest input (n * (2 + i.val * (1 + forsHeight) + j.val)) }
      hypertree := fun i => {
        wots := fun j =>
          readDigest input
            (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) + j.val))
        authentication := fun j =>
          readDigest input
            (n * (1 + forsTrees * (1 + forsHeight) + i.val * (chains + subtreeHeight) +
              chains + j.val)) } }
  else none

end SlhDsaSecurity

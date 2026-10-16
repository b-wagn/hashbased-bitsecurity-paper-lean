import XmssSecurity.Statement.Scheme.Xmss

/-!
# The checksummed construction in the shape used by the proofs

The proofs were written for an encoding that can reject a digest and a signer that retries. This
file restates the construction of `Statement/Scheme/Construction.lean` in that shape:

* `Checksum.decodeDigest` decodes every digest, to its checksummed encoding;
* `Checksum.Valid` is membership in the code: the last message digit has only two bits, and the
  checksum digits are those of the checksum of the message digits;
* `Concrete.precomputedSignAttempt` and `Seeded.signFrom` are the one-attempt signer and the
  retry loop, with `signingAttemptLimit = 1`.

`Seeded.sign_eq_signFrom` and `Concrete.verify_eq_decode` identify the statement's algorithms with
these forms.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- `A_max`: the signer makes a single encoding attempt. -/
def signingAttemptLimit : Nat := 1

namespace Checksum

/-- Every digest decodes, to its checksummed encoding. -/
def decodeDigest (digest : Digest) : Option Encoding := some (encode digest)

/-- The chain carrying message digit `i`. -/
def messageChain (i : Fin messageDigits) : ChainIndex :=
  ⟨i.val, by have := i.isLt; simp only [numChains, messageDigits] at *; omega⟩

/-- The chain carrying checksum digit `j`. -/
def checksumChain (j : Fin checksumDigits) : ChainIndex :=
  ⟨messageDigits + j.val, by have := j.isLt; simp only [numChains, messageDigits, checksumDigits] at *; omega⟩

/-- The message digits of a word. -/
def messagePart (x : Encoding) : Fin messageDigits → Digit := fun i => x (messageChain i)

/-- The last message digit, which has only the digest bits `126` and `127`. -/
def lastMessageDigit : Fin messageDigits := ⟨messageDigits - 1, by decide⟩

/-- Membership in the code `C`: the last message digit is below `4`, and the checksum digits are
the base-`2^w` digits of the checksum of the message digits. -/
def Valid (x : Encoding) : Prop :=
  (x (messageChain lastMessageDigit)).val < 4 ∧
    ∀ j, x (checksumChain j) = checksumDigit (checksum (messagePart x)) j

instance : DecidablePred Valid := fun _ => by unfold Valid; infer_instance

end Checksum

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One attempt: hash once, and sign the decoded encoding. -/
def precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := Checksum.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

/-- The verifier, with the decoding step written out. -/
theorem verify_eq_decode (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) :
    (verify publicKey leafIndex message signature : m Bool) = (do
      let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
      let some encoding := Checksum.decodeDigest digest | return false
      let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
      let leaf ← leafHash publicKey.parameter leafIndex endpoints
      verifyAfterLeaf publicKey leafIndex signature leaf) := rfl

end Concrete

namespace Seeded

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex
        message (BitVec.ofNat 32 trial)
      match ← Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message attempts (trial + 1)

theorem sign_eq_signFrom [LawfulMonad m] (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) :
    (sign secretKey leafIndex message : m (Option Signature)) =
      signFrom secretKey leafIndex message signingAttemptLimit 0 := by
  simp only [sign, signFrom, signingAttemptLimit, Concrete.precomputedSignAttempt,
    Checksum.decodeDigest, bind_assoc, pure_bind]
  rfl

end Seeded

end XmssSecurity

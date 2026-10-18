import XmssSecurity.Statement.Scheme.Checksum

/-!
# The checksummed code in the shape used by the proofs

* `Checksum.decodeDigest` decodes every digest, to its checksummed encoding;
* `Checksum.Valid` is membership in the code: the last message digit has only two bits, and the
  checksum digits are those of the checksum of the message digits;
* the signer makes a single attempt: `signingAttemptLimit = 1`.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Checksum

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

end XmssSecurity.Checksum

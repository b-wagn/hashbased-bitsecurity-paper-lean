import Xmss.Statement.Scheme.Checksum

/-!
# The checksummed code in the shape used by the proofs

`Checksum.Valid` is membership in the code: each message digit has four bits, and the
checksum digits are those of the checksum of the message digits. The chain indices
`messageChain` and `checksumChain` name the two parts of a codeword.
-/

open OracleComp OracleSpec

namespace Xmss.Checksum

/-- The chain carrying message digit `i`. -/
def messageChain (i : Fin messageDigits) : ChainIndex :=
  ⟨i.val, by have := i.isLt; simp only [numChains, messageDigits] at *; omega⟩

/-- The chain carrying checksum digit `j`. -/
def checksumChain (j : Fin checksumDigits) : ChainIndex :=
  ⟨messageDigits + j.val, by have := j.isLt; simp only [numChains, messageDigits, checksumDigits] at *; omega⟩

/-- The message digits of a word. -/
def messagePart (x : Encoding) : Fin messageDigits → Digit := fun i => x (messageChain i)

/-- Membership in the code: the final three digits are the base-16 checksum digits. -/
def Valid (x : Encoding) : Prop :=
  ∀ j, x (checksumChain j) = checksumDigit (checksum (messagePart x)) j

instance : DecidablePred Valid := fun _ => by unfold Valid; infer_instance

end Xmss.Checksum

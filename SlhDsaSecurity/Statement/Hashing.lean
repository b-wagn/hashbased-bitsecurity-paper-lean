import SlhDsaSecurity.Statement.Address
import Xmss.Statement.RandomOracleModel

/-!
# One shared ideal hash for the SHAKE byte formats

The oracle returns 30 bytes. A short hash retains the first 16 bytes of that same answer;
repeated inputs and overlapping function roles therefore remain consistent. One call costs
one unit regardless of input length. This idealization is not a concrete SHAKE security claim.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity

abbrev HashSpec := Xmss.RandomOracleModel.HashSpec Bytes HashOutput
abbrev OracleWorld := Xmss.RandomOracleModel.World Bytes HashOutput

namespace Hashing

/-- First 16 bytes of the 30-byte oracle answer, in big-endian order. -/
def truncate (answer : HashOutput) : Digest :=
  answer.extractLsb' (8 * (messageDigestBytes - n)) (8 * n)

/-- Shared by F, H, T_l and PRF. Address types distinguish their structural uses. -/
def tweakableInput (seed : Digest) (address : Address) (payload : Bytes) : Bytes :=
  bytesBE n seed ++ address.toBytes ++ payload

/-- Deterministic PRF_msg, with opt_rand = PK.seed. -/
def randomizerInput (prf seed : Digest) (message : Bytes) : Bytes :=
  bytesBE n prf ++ bytesBE n seed ++ message

def messageInput (randomizer : Digest) (pk : PublicKey) (message : Bytes) : Bytes :=
  bytesBE n randomizer ++ bytesBE n pk.seed ++ bytesBE n pk.root ++ message

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def hash (input : Bytes) : m HashOutput := query (spec := HashSpec) input

def shortHash (input : Bytes) : m Digest := do
  return truncate (← hash input)

def tweakable (seed : Digest) (address : Address) (payload : Bytes) : m Digest :=
  shortHash (tweakableInput seed address payload)

def derive (publicSeed secretSeed : Digest) (address : Address) : m Digest :=
  tweakable publicSeed address (bytesBE n secretSeed)

def randomizer (prf seed : Digest) (message : Bytes) : m Digest :=
  shortHash (randomizerInput prf seed message)

def messageDigest (randomizer : Digest) (pk : PublicKey) (message : Bytes) : m HashOutput :=
  hash (messageInput randomizer pk message)

end Hashing

/-- Pure SLH-DSA framing, FIPS 205 Algorithms 22 and 24. -/
def Message.frame (request : Message) : Option Bytes :=
  if request.context.length ≤ 255 then
    some ([0, UInt8.ofNat request.context.length] ++ request.context ++ request.message)
  else none

end SlhDsaSecurity

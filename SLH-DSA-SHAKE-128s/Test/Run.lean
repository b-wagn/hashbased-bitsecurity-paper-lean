import «SLH-DSA-SHAKE-128s».Statement.Scheme
import «SLH-DSA-SHAKE-128s».Test.Shake

/-!
# Running the specification on NIST's ACVP test vectors

The random oracle is instantiated with SHAKE256: a 30-byte answer, whose 16-byte prefix is the
short hash, exactly as in the specification. `vectors.txt` holds the SLH-DSA-SHAKE-128s cases of
the ACVP key generation, deterministic signing and verification tests.
-/

open SlhDsaSecurity OracleComp

namespace SlhDsaTest

/-- The oracle is SHAKE256 with a 30-byte output, read big-endian. -/
def shakeAnswer (input : Bytes) : HashOutput :=
  (shake256 (ByteArray.mk input.toArray) messageDigestBytes).toList.foldl
    (fun (value : HashOutput) byte => (value <<< 8) ||| BitVec.ofNat _ byte.toNat) 0

/-- The spec runs in `IO`, a strict monad: in `Id` the compiler eta-expands the function-valued
results of `sequenceFin` and recomputes their entries on every access. -/
instance : HasQuery HashSpec IO where
  query input := pure (shakeAnswer input)

def parseHex (s : String) : Option Bytes :=
  if s = "-" then some [] else
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → Option Bytes
    | [] => some []
    | a :: b :: rest => do
      let hi ← digit a
      let lo ← digit b
      return (hi * 16 + lo).toUInt8 :: (← go rest)
    | [_] => none
  go s.toList

def toDigest (bytes : Bytes) : Digest :=
  bytes.foldl (fun value byte => (value <<< 8) ||| BitVec.ofNat _ byte.toNat) 0

/-- `PK.seed ‖ PK.root`. -/
def toPublicKey (bytes : Bytes) : PublicKey :=
  { seed := toDigest (bytes.take 16), root := toDigest (bytes.drop 16) }

/-- `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
def toSecretKey (bytes : Bytes) : SecretKey :=
  { seed := toDigest (bytes.take 16), prf := toDigest ((bytes.drop 16).take 16),
    publicKey := toPublicKey (bytes.drop 32) }

def hex (s : String) : IO Bytes := do
  let some bytes := parseHex s | throw (IO.userError s!"bad hex: {s.take 20}")
  return bytes

/-- Run one line of `vectors.txt`. -/
def check (line : String) : IO Bool := do
  match line.splitOn " " with
  | ["keygen", _, skSeed, skPrf, pkSeed, pk] =>
    let (_, key) ← Scheme.keygenInternal (m := IO) (toDigest (← hex skSeed))
      (toDigest (← hex skPrf)) (toDigest (← hex pkSeed))
    return key == toPublicKey (← hex pk)
  | ["sign", _, sk, message, context, signature] =>
    let request : Message := { message := ← hex message, context := ← hex context }
    return (← Scheme.sign (m := IO) (toSecretKey (← hex sk)) request) == some (← hex signature)
  | ["signInternal", _, sk, message, signature] =>
    let signed ← Scheme.signInternal (m := IO) (toSecretKey (← hex sk)) (← hex message)
    return signed.toBytes == (← hex signature)
  | ["verify", _, pk, message, context, signature, expected] =>
    let request : Message := { message := ← hex message, context := ← hex context }
    let accepted ← Scheme.verify (m := IO) (toPublicKey (← hex pk)) request (← hex signature)
    return accepted == (expected == "true")
  | ["verifyInternal", _, pk, message, signature, expected] =>
    let accepted ← match Signature.fromBytes? (← hex signature) with
      | none => pure false
      | some parsed => Scheme.verifyInternal (m := IO) (toPublicKey (← hex pk)) (← hex message) parsed
    return accepted == (expected == "true")
  | _ => throw (IO.userError "unknown test kind")

end SlhDsaTest

open SlhDsaTest in
def main (args : List String) : IO UInt32 := do
  let path := args.headD "SLH-DSA-SHAKE-128s/Test/vectors.txt"
  let only := args.drop 1
  let mut failures := 0
  let mut count := 0
  for line in (← IO.FS.lines path) do
    let fields := line.splitOn " "
    if line.isEmpty || (!only.isEmpty && !only.contains (fields.headD "")) then continue
    let label := s!"{fields.headD ""} {fields.getD 1 ""}"
    match ← (check line).toBaseIO with
    | .ok true => count := count + 1; IO.println s!"ok   {label}"
    | .ok false => failures := failures + 1; IO.println s!"FAIL {label}"
    | .error e => failures := failures + 1; IO.println s!"BAD  {label}: {e}"
    (← IO.getStdout).flush
  IO.println s!"{count} passed, {failures} failed"
  return if failures = 0 then 0 else 1

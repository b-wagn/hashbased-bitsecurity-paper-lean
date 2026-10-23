import SlhDsaSecurity.Statement.Scheme

/-!
# The correctness game

Key generation, signing and byte-facing verification, all against one shared lazy random oracle,
with the three key-generation seeds drawn as private uniform samples. A request whose context is
too long is rejected by the signer (`none`), which is kept distinct from a signature that fails
verification (`some false`).
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CorrectnessGame

section Algorithms

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Sign a request with the keys, and verify what the signer returns. -/
def signAndVerify (keys : SecretKey × PublicKey) (request : Message) : m (Option Bool) := do
  match ← Scheme.sign keys.1 request with
  | none => return none
  | some signature => return some (← Scheme.verify keys.2 request signature)

/-- The round trip at fixed key-generation seeds. -/
def roundTrip (secretSeed prfSeed publicSeed : Digest) (request : Message) : m (Option Bool) := do
  let keys ← Scheme.keygenInternal secretSeed prfSeed publicSeed
  signAndVerify keys request

end Algorithms

/-- **The correctness experiment**: actual randomized key generation, then the round trip. -/
noncomputable def experiment (request : Message) : OracleComp OracleWorld (Option Bool) := do
  let keys ← Scheme.keygen
  signAndVerify keys request

end SlhDsaSecurity.CorrectnessGame

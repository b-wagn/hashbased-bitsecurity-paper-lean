import SlhDsaSecurity.Statement.Scheme
import SlhDsaSecurity.Proof.Signature
import SlhDsaSecurity.Proof.Correctness.Fors
import SlhDsaSecurity.Proof.Correctness.Hypertree

/-!
# Deterministic algorithm correctness

For every fixed hash and every three key-generation seeds, signing a valid pure-SLH-DSA
message produces bytes accepted by the standard byte-facing verifier. This module does
not yet connect the fixed-hash interpretation to the lazy-sampled shared-ROM experiment.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Correctness.Scheme

variable [HasQuery HashSpec Id]

theorem verifyInternal_signInternal (sk : SecretKey) (message : Bytes)
    (hroot : sk.publicKey.root = SlhDsaSecurity.Merkle.node (m := Id) sk.seed sk.publicKey.seed
      (SlhDsaSecurity.Hypertree.address (layers - 1) 0) subtreeHeight 0) :
    SlhDsaSecurity.Scheme.verifyInternal (m := Id) sk.publicKey message
        (SlhDsaSecurity.Scheme.signInternal (m := Id) sk message) = true := by
  simp only [SlhDsaSecurity.Scheme.signInternal, SlhDsaSecurity.Scheme.verifyInternal,
    bind, pure]
  exact Hypertree.verify_sign _ _ _ _ _ hroot

theorem verify_sign (sk : SecretKey) (request : Message) (message : Bytes)
    (hframe : request.frame = some message)
    (hroot : sk.publicKey.root = SlhDsaSecurity.Merkle.node (m := Id) sk.seed sk.publicKey.seed
      (SlhDsaSecurity.Hypertree.address (layers - 1) 0) subtreeHeight 0) :
    ∃ signature : Bytes,
      SlhDsaSecurity.Scheme.sign (m := Id) sk request = some signature ∧
      SlhDsaSecurity.Scheme.verify (m := Id) sk.publicKey request signature = true := by
  refine ⟨(SlhDsaSecurity.Scheme.signInternal (m := Id) sk message).toBytes, ?_, ?_⟩
  · simp only [SlhDsaSecurity.Scheme.sign, hframe, bind, pure]
  · simp only [SlhDsaSecurity.Scheme.verify, hframe, Signature.fromBytes_toBytes]
    exact verifyInternal_signInternal sk message hroot

/-- All seeds and all valid contexts are covered; the root is computed by actual keygen. -/
theorem verify_sign_keygen (secretSeed prfSeed publicSeed : Digest) (request : Message)
    (hcontext : request.context.length ≤ 255) :
    let keys := SlhDsaSecurity.Scheme.keygenInternal (m := Id) secretSeed prfSeed publicSeed
    ∃ signature : Bytes,
      SlhDsaSecurity.Scheme.sign (m := Id) keys.1 request = some signature ∧
      SlhDsaSecurity.Scheme.verify (m := Id) keys.2 request signature = true := by
  apply verify_sign _ request
    ([0, UInt8.ofNat request.context.length] ++ request.context ++ request.message)
  · exact if_pos hcontext
  · rfl

end SlhDsaSecurity.Correctness.Scheme

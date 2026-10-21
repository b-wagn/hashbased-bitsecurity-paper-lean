import SlhDsaSecurity.Proof.FramingClosure
import SlhDsaSecurity.Proof.FramingOverlap

/-!
# The signer's randomizer is a message digest for another message

FIPS 205 Section 11.1 fixes the byte inputs

* `PRF_msg(SK.prf, PK.seed, M') = SHAKE(SK.prf ‖ PK.seed ‖ M')`
* `H_msg(R, PK.seed, PK.root, M') = SHAKE(R ‖ PK.seed ‖ PK.root ‖ M')`

Idealising SHAKE as one shared random oracle, as the experiment does, makes these two
input families overlap: taking `R = SK.prf` and `M' = PK.root ‖ m` turns the first input
into the second on `m`. The identity is unconditional list algebra
(`randomizerInput_eq_messageInput`). Consequently the randomizer the honest signer
publishes on the request framed as `PK.root ‖ m` is *exactly* the sixteen-byte truncation
of the thirty-byte message digest that a verifier computes for the message `m` with
randomizer field `SK.prf` (`randomizer_eq_truncate_messageDigest`).

When `PK.root` begins with a zero byte — probability exactly `1/256` under actual key
generation, by `FramingOverlap.keygen_zero_probability` — such a request is a *legal* pure
SLH-DSA request (`exists_legal_request`), so the signer really does answer it, and the
signing query is free: it is not charged to `q`.

This is a structural leak in the shared-oracle idealisation, stated and proved here as a
deterministic fact about the specified byte formats. It is not by itself a forgery: using
the leaked digest requires the verifier's randomizer field to equal `SK.prf`. The
quantitative consequence is recorded in `Proof/SharedOracleArithmetic.lean`.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.FramingLeak

/-- The specified PRF-message and message-hash byte inputs coincide when the randomizer is
the signer's PRF seed and the signed message is the public root followed by `m`. This needs
no hypothesis: it is an identity of the FIPS 205 input formats. -/
theorem randomizerInput_eq_messageInput (prf : Digest) (pk : PublicKey) (message : Bytes) :
    Hashing.randomizerInput prf pk.seed (bytesBE n pk.root ++ message) =
      Hashing.messageInput prf pk message := by
  simp only [Hashing.randomizerInput, Hashing.messageInput, List.append_assoc]

/-- The randomizer published by the honest signer on the request framed as `PK.root ‖ m`
equals the truncated message digest of `m` under randomizer field `SK.prf`. -/
theorem randomizer_eq_truncate_messageDigest [HasQuery HashSpec Id]
    (prf : Digest) (pk : PublicKey) (message : Bytes) :
    Hashing.randomizer (m := Id) prf pk.seed (bytesBE n pk.root ++ message) =
      Hashing.truncate (Hashing.messageDigest (m := Id) prf pk message) := by
  unfold Hashing.randomizer Hashing.messageDigest Hashing.shortHash Hashing.hash
  rw [randomizerInput_eq_messageInput]
  rfl

/-- A zero leading byte of the public root makes `PK.root ‖ m` a legal pure request, for
every message of at least 257 bytes. The signer therefore answers it, free of charge. -/
theorem exists_legal_request (pk : PublicKey) (message : Bytes)
    (hzero : FramingOverlap.firstByte pk.root = 0) (hlength : 257 ≤ message.length) :
    ∃ request : Message, request.frame = some (bytesBE n pk.root ++ message) :=
  FramingClosure.prepend_digest_exists_frame pk.root message hzero hlength

/-- Both facts together: under the zero-leading-byte condition there is a legal request
whose honest randomizer is the truncated digest of `message` under randomizer `SK.prf`. -/
theorem exists_legal_request_leaking_digest [HasQuery HashSpec Id]
    (prf : Digest) (pk : PublicKey) (message : Bytes)
    (hzero : FramingOverlap.firstByte pk.root = 0) (hlength : 257 ≤ message.length) :
    ∃ request : Message, ∃ framed : Bytes,
      request.frame = some framed ∧
      Hashing.randomizer (m := Id) prf pk.seed framed =
        Hashing.truncate (Hashing.messageDigest (m := Id) prf pk message) := by
  obtain ⟨request, hframe⟩ := exists_legal_request pk message hzero hlength
  exact ⟨request, bytesBE n pk.root ++ message, hframe,
    randomizer_eq_truncate_messageDigest prf pk message⟩

/-- The whole `chainFrame` family is legal at once: each of its members is a pure request
whose honest randomizer is the truncated digest of the next member down. This is what lets
a single run of free signing queries harvest many such values. -/
theorem chainFrame_legal (pk : PublicKey) (base : Bytes)
    (hzero : FramingOverlap.firstByte pk.root = 0) (hlength : 257 ≤ base.length)
    (hbase : ∃ request : Message, request.frame = some base) (step : Nat) :
    ∃ request : Message,
      request.frame = some (FramingClosure.chainFrame pk.root base step) :=
  FramingClosure.chainFrame_exists_frame pk.root base hzero hlength hbase step

/-- Each step of the chain leaks the truncated digest of the previous step. -/
theorem chainFrame_randomizer_eq [HasQuery HashSpec Id]
    (prf : Digest) (pk : PublicKey) (base : Bytes) (step : Nat) :
    Hashing.randomizer (m := Id) prf pk.seed
        (FramingClosure.chainFrame pk.root base (step + 1)) =
      Hashing.truncate (Hashing.messageDigest (m := Id) prf pk
        (FramingClosure.chainFrame pk.root base step)) := by
  rw [show FramingClosure.chainFrame pk.root base (step + 1) =
    bytesBE n pk.root ++ FramingClosure.chainFrame pk.root base step from rfl]
  exact randomizer_eq_truncate_messageDigest prf pk _

end SlhDsaSecurity.FramingLeak

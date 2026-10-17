import XmssSecurity.Proof.TargetSum.CappedUnifiedStructuralCollision

/-!
# The deciding path of a forgery

Vocabulary for the 122-bit direct-mode proof (`docs/plan-direct-122.md`). For a forgery at leaf
index `idx*` with encoding `x*`, and the signature the signer returned at `idx*` (if any) with
encoding `x`:

* chain `i` is *trivial* when `x_i ≤ x*_i` and the forged chain value is the honest value at
  digit `x*_i`, which the adversary can compute from the returned signature;
* the *deciding chain* `i0` is the smallest non-trivial chain (chain `0` if every chain is
  trivial, which forces the encoding event);
* `DecidingChainValueRevealed`: at the deciding chain the forged digit is below the signed digit
  (or nothing was returned at `idx*`) and the forged value is the honest hidden value;
* the *deciding inputs* are the chain inputs of chain `i0` at `idx*`, the leaf input at `idx*`,
  and the Merkle inputs on the path of `idx*`; `decidingTargetInput` moves exactly those as
  `keygenStructuralTargetInput` does and fixes every other input.
-/

open OracleComp OracleSpec

namespace XmssSecurity.TargetSum.Deciding

open Concrete

/-- The request and signature the signer returned at `leafIndex`, if any. A valid transcript has
at most one request per leaf index. -/
def returnedAt (log : QueryLog SigningSpec) (leafIndex : LeafIndex) :
    Option (SignRequest × Signature) :=
  log.findSome? fun entry =>
    match entry.2 with
    | some signature => if entry.1.epoch = leafIndex then some (entry.1, signature) else none
    | none => none

/-- The encoding of the signature returned at `leafIndex`, read from the cache. -/
noncomputable def signedEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (leafIndex : LeafIndex) : Option Encoding :=
  match returnedAt log leafIndex with
  | none => none
  | some (request, signature) =>
      TargetSum.decodeDigest
        (CacheView.encodingHash cache parameter leafIndex (request.message, signature.randomness))

/-- The encoding of the forgery, read from the cache. -/
noncomputable def forgedEncoding (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (forgery : Forgery) : Option Encoding :=
  TargetSum.decodeDigest
    (CacheView.encodingHash cache parameter forgery.epoch
      (forgery.message, forgery.signature.randomness))

/-- The honest chain value of chain `chain` at `leafIndex` at `digit`, replayed from the cache. -/
noncomputable def honestChainValue (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit) : Digest :=
  Wots.signChain (CacheView.chainStep cache secretKey.parameter leafIndex chain) digit
    (secretKey.chainStart leafIndex chain)

/-- Chain `chain` of the forgery is trivial: a signature was returned at the forgery's leaf index,
its digit there is at most the forged digit, and the forged value is the honest value at the
forged digit. -/
def ChainTrivial (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (forgedEnc : Encoding)
    (chain : ChainIndex) : Prop :=
  ∃ signedEnc, signedEncoding cache secretKey.parameter log forgery.epoch = some signedEnc ∧
    signedEnc chain ≤ forgedEnc chain ∧
    forgery.signature.chainValue chain =
      honestChainValue cache secretKey forgery.epoch chain (forgedEnc chain)

open Classical in
/-- The smallest non-trivial chain, if any. -/
noncomputable def decidingChain? (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (forgedEnc : Encoding) :
    Option ChainIndex :=
  (List.finRange numChains).find? fun chain =>
    decide (¬ChainTrivial cache secretKey log forgery forgedEnc chain)

/-- The deciding chain, chain `0` if every chain is trivial. -/
noncomputable def decidingChain (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (forgery : Forgery) (forgedEnc : Encoding) : ChainIndex :=
  (decidingChain? cache secretKey log forgery forgedEnc).getD ⟨0, by simp [numChains]⟩

/-- The deciding chain of an outcome, from the forged encoding in the cache (chain `0` if the
forged encoding does not decode). -/
noncomputable def outcomeDecidingChain (cache : QueryCache HashSpec) (outcome : GameOutcome) :
    ChainIndex :=
  match forgedEncoding cache outcome.secretKey.parameter outcome.forgery with
  | none => ⟨0, by simp [numChains]⟩
  | some forgedEnc =>
      decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery forgedEnc

/-- The forged value at the deciding chain is a hidden honest value: the forged digit is below the
signed digit there (or no signature was returned at the forgery's leaf index), and the forged
value is the honest value at the forged digit. -/
def DecidingChainValueRevealed (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ forgedEnc, forgedEncoding cache outcome.secretKey.parameter outcome.forgery = some forgedEnc ∧
    let chain := decidingChain cache outcome.secretKey outcome.signingLog outcome.forgery forgedEnc
    (∀ signedEnc, signedEncoding cache outcome.secretKey.parameter outcome.signingLog
        outcome.forgery.epoch = some signedEnc → forgedEnc chain < signedEnc chain) ∧
    outcome.forgery.signature.chainValue chain =
      honestChainValue cache outcome.secretKey outcome.forgery.epoch chain (forgedEnc chain)

/-- The hash inputs on the deciding path: chain inputs of the deciding chain at the forgery's leaf
index, the leaf input there, and the Merkle inputs on its authentication path. -/
def IsDecidingInput (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) : Prop :=
  (∃ (step : ChainStep) (value : Digest),
      input = CacheView.chainInput parameter leafIndex chain step value) ∨
  (∃ endpoints : ChainIndex → Digest, input = CacheView.leafInput parameter leafIndex endpoints) ∨
  (∃ (level : MerkleLevel) (left right : Digest),
      input = CacheView.merkleInput parameter level (Concrete.nodeIndex leafIndex level.val)
        left right)

open Classical in
/-- `keygenStructuralTargetInput` on the deciding inputs, the identity elsewhere. -/
noncomputable def decidingTargetInput (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (input : HashInput) : HashInput :=
  if IsDecidingInput secretKey.parameter leafIndex chain input then
    keygenStructuralTargetInput secretKey cache input
  else input

theorem isDecidingInput_of_decidingTargetInput_ne (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (hne : decidingTargetInput secretKey cache leafIndex chain input ≠ input) :
    IsDecidingInput secretKey.parameter leafIndex chain input := by
  unfold decidingTargetInput at hne
  split at hne
  · assumption
  · exact (hne rfl).elim

theorem decidingTargetInput_eq_structural_of_isDecidingInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (h : IsDecidingInput secretKey.parameter leafIndex chain input) :
    decidingTargetInput secretKey cache leafIndex chain input =
      keygenStructuralTargetInput secretKey cache input := by
  unfold decidingTargetInput
  rw [if_pos h]

/-- A collision with the deciding map is a collision with the structural map. -/
theorem adaptiveFreshDigestCollisionWith_structural_of_deciding
    (initialCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (chain : ChainIndex)
    (h : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (decidingTargetInput secretKey cache leafIndex chain)) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      (keygenStructuralTargetInput secretKey cache) :=
  adaptiveFreshDigestCollisionWith_of_target_eq initialCache finalCache _ _
    (fun input hne => (decidingTargetInput_eq_structural_of_isDecidingInput secretKey cache
      leafIndex chain input (isDecidingInput_of_decidingTargetInput_ne secretKey cache leafIndex
        chain input hne)).symm) h

end XmssSecurity.TargetSum.Deciding

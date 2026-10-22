import SlhDsaSecurity.Proof.HonestProbes

/-!
# What format the verifier's queries are in

`HonestProbes` characterises the honest parties' queries by *what they are* — canonical inputs of
the graph, or the two message-dependent ones signing makes. That is the right characterisation
for key generation and the signer, whose inputs are built from the real secrets, and it is
useless for the verifier, whose inputs are built from a forgery's values and need not be
canonical at all.

What is true of the verifier, and is all that is needed, is weaker and purely syntactic: apart
from the single message digest, every call it makes is `Hashing.tweakable` at the public key's
seed, so every probe opens with `PK.seed`. That holds whatever the signature contains, since the
format of a call does not depend on the values being hashed.

It is wanted for provenance. A `PRF_msg` input opens with `SK.prf`, so when the two seeds differ
no verifier query is one — except the message digest, which is a `PRF_msg` input at its own
randomiser read as the seed and so is one exactly when the forgery's randomiser *is* `SK.prf`.
`verify_probe_randomizerInput` is that statement, and it is the shape the randomiser defect's
provenance consumes: a `PRF_msg` entry the verifier made is the forgery's own digest query.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerifierFormat

open CacheReplay HonestProbes

/-- A probe in the tweakable format at a fixed seed: `PK.seed ‖ ADRS ‖ payload`. -/
def TweakableAt (publicSeed : Digest) (probe : Bytes) : Prop :=
  ∃ (address : Address) (payload : Bytes),
    probe = Hashing.tweakableInput publicSeed address payload

theorem tweakableAt_input (publicSeed : Digest) (address : Address) (payload : Bytes) :
    TweakableAt publicSeed (Hashing.tweakableInput publicSeed address payload) :=
  ⟨address, payload, rfl⟩

/-! ## The components, at any values at all -/

/-- **A WOTS chain consults tweakable inputs**, wherever it starts and whatever it starts from. -/
theorem probes_chain (cache : QueryCache HashSpec) (publicSeed : Digest) (address : Address) :
    ∀ (steps start : Nat) (value : Digest),
      Probes cache
        (Wots.chain (m := OracleComp HashSpec) publicSeed address start steps value)
        (TweakableAt publicSeed) := by
  intro steps
  induction steps with
  | zero => intro start value; exact probes_pure cache _ _
  | succ steps ih =>
    intro start value
    rw [Wots.chain]
    exact probes_tweakable cache publicSeed _ _ _ _ (tweakableAt_input _ _ _) (ih _ _)

/-- **Recovering a WOTS public key consults tweakable inputs.** -/
theorem probes_wots_fromSignature (cache : QueryCache HashSpec) (signature : WotsSignature)
    (message publicSeed : Digest) (address : Address) :
    Probes cache
      (Wots.publicKeyFromSignature (m := OracleComp HashSpec) signature message publicSeed
        address)
      (TweakableAt publicSeed) := by
  refine probes_bind_replay cache _ _ _
    (probes_sequenceFin cache _ chains _ fun i => probes_chain cache publicSeed _ _ _ _) ?_
  exact probes_tweakable_self cache publicSeed _ _ _ (tweakableAt_input _ _ _)

/-- **Recovering a subtree root from an XMSS signature consults tweakable inputs.** -/
theorem probes_merkle_fromSignature (cache : QueryCache HashSpec)
    (index : Fin (2 ^ subtreeHeight)) (signature : XmssSignature) (message publicSeed : Digest)
    (address : Address) :
    Probes cache
      (Merkle.publicKeyFromSignature (m := OracleComp HashSpec) index signature message
        publicSeed address)
      (TweakableAt publicSeed) := by
  refine probes_bind_replay cache _ _ _
    (probes_wots_fromSignature cache signature.wots message publicSeed _) ?_
  exact probes_foldlM cache
    (fun value j => Hashing.tweakableInput publicSeed
      (Merkle.nodeAddress address (j.val + 1) (index.val / 2 ^ (j.val + 1)))
      (if index.val / 2 ^ j.val % 2 = 0 then
        bytesBE n value ++ bytesBE n (signature.authentication j)
        else bytesBE n (signature.authentication j) ++ bytesBE n value))
    _ (List.finRange subtreeHeight) _ fun k hk => tweakableAt_input _ _ _

/-- **Recovering a FORS public key consults tweakable inputs.** -/
theorem probes_fors_fromSignature (cache : QueryCache HashSpec) (signature : ForsSignature)
    (indices : Fors.Indices) (publicSeed : Digest) (address : Address) :
    Probes cache
      (Fors.publicKeyFromSignature (m := OracleComp HashSpec) signature indices publicSeed
        address)
      (TweakableAt publicSeed) := by
  refine probes_bind_replay cache _ _ _
    (probes_sequenceFin cache _ forsTrees _ fun i => ?_) ?_
  · refine probes_tweakable cache publicSeed _ _ _ _ (tweakableAt_input _ _ _) ?_
    exact probes_foldlM cache
      (fun value j => Hashing.tweakableInput publicSeed
        (Fors.nodeAddress address (j.val + 1)
          ((i.val * 2 ^ forsHeight + (indices i).val) / 2 ^ (j.val + 1)))
        (if (indices i).val / 2 ^ j.val % 2 = 0 then
          bytesBE n value ++ bytesBE n ((signature i).authentication j)
          else bytesBE n ((signature i).authentication j) ++ bytesBE n value))
      _ (List.finRange forsHeight) _ fun k hk => tweakableAt_input _ _ _
  · exact probes_tweakable_self cache publicSeed _ _ _ (tweakableAt_input _ _ _)

/-- **Climbing the hypertree consults tweakable inputs**, at every layer and whatever the
signatures hold. -/
theorem probes_rootFromSignature (cache : QueryCache HashSpec) (publicSeed : Digest) :
    ∀ (remaining : Nat) (signatures : Fin remaining → XmssSignature) (layer tree : Nat)
      (leaf : Hypertree.LeafIndex) (message : Digest),
      Probes cache
        (Hypertree.rootFromSignature (m := OracleComp HashSpec) publicSeed remaining signatures
          layer tree leaf message)
        (TweakableAt publicSeed) := by
  intro remaining
  induction remaining with
  | zero => intro signatures layer tree leaf message; exact probes_pure cache _ _
  | succ remaining ih =>
    intro signatures layer tree leaf message
    rw [Hypertree.rootFromSignature]
    exact probes_bind_replay cache _ _ _
      (probes_merkle_fromSignature cache leaf (signatures 0) message publicSeed _) (ih _ _ _ _ _)

/-- **The hypertree check consults tweakable inputs.** -/
theorem probes_hypertree_verify (cache : QueryCache HashSpec) (message : Digest)
    (signature : HypertreeSignature) (pk : PublicKey) (tree : Hypertree.TreeIndex)
    (leaf : Hypertree.LeafIndex) :
    Probes cache
      (Hypertree.verify (m := OracleComp HashSpec) message signature pk tree leaf)
      (TweakableAt pk.seed) :=
  probes_bind_replay cache _ _ _
    (probes_rootFromSignature cache pk.seed layers signature 0 tree.toNat leaf message)
    (probes_pure cache _ _)

/-! ## The verifier -/

/-- **Every input the verifier consults is tweakable at `PK.seed`, bar the message digest.** -/
theorem probes_verifyInternal (cache : QueryCache HashSpec) (pk : PublicKey) (message : Bytes)
    (parsed : Signature) :
    Probes cache (Scheme.verifyInternal (m := OracleComp HashSpec) pk message parsed)
      (fun probe => probe = Hashing.messageInput parsed.randomizer pk message ∨
        TweakableAt pk.seed probe) := by
  refine probes_hash cache _ _ _ (Or.inl rfl) ?_
  refine probes_bind_replay cache _ _ _
    (Probes.mono (probes_fors_fromSignature cache parsed.fors _ pk.seed _)
      fun _ hprobe => Or.inr hprobe) ?_
  exact Probes.mono (probes_hypertree_verify cache _ parsed.hypertree pk _ _)
    fun _ hprobe => Or.inr hprobe

/-- The same for a request, which the verifier frames and parses before any call. -/
theorem probes_verify (cache : QueryCache HashSpec) (pk : PublicKey) (request : Message)
    (signature : Bytes) :
    Probes cache (Scheme.verify (m := OracleComp HashSpec) pk request signature)
      (fun probe => (∃ (framed : Bytes) (parsed : Signature), request.frame = some framed ∧
          Signature.fromBytes? signature = some parsed ∧
          probe = Hashing.messageInput parsed.randomizer pk framed) ∨
        TweakableAt pk.seed probe) := by
  rw [Scheme.verify]
  cases hframe : request.frame with
  | none => exact probes_pure cache _ _
  | some framed =>
    cases hparsed : Signature.fromBytes? signature with
    | none => exact probes_pure cache _ _
    | some parsed =>
      exact Probes.mono (probes_verifyInternal cache pk framed parsed) fun probe hprobe =>
        hprobe.imp (fun heq => ⟨framed, parsed, rfl, rfl, heq⟩) id

/-- **A `PRF_msg` input the verifier consults is the forgery's own digest query.** The two seeds
being distinct, no tweakable input is a `PRF_msg` one, so the only candidate left is the message
digest — which is a `PRF_msg` input exactly when the forgery's randomiser is the seed. -/
theorem verify_probe_randomizerInput (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (prfSeed seed : Digest) (message : Bytes)
    (hne : prfSeed ≠ pk.seed) {probe : Bytes}
    (hprobe : QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request signature)
      probe)
    (hformat : probe = Hashing.randomizerInput prfSeed seed message) :
    ∃ (framed : Bytes) (parsed : Signature), request.frame = some framed ∧
      Signature.fromBytes? signature = some parsed ∧
      probe = Hashing.messageInput parsed.randomizer pk framed := by
  rcases probes_verify cache pk request signature probe hprobe with hdigest | ⟨address, payload,
    htweakable⟩
  · exact hdigest
  · exact absurd (hformat ▸ htweakable : Hashing.randomizerInput prfSeed seed message =
      Hashing.tweakableInput pk.seed address payload) (HashSeparation.randomizer_tweakable_ne hne)

end SlhDsaSecurity.VerifierFormat

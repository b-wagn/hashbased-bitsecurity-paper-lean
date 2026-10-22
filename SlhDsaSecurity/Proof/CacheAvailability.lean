import SlhDsaSecurity.Proof.ClaimedProbes
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.LazyBudget

/-!
# Availability, read off the cache

`OpenCache.lazyProgram` reads availability off the cache it carries, while
`CanonicalGraph.Available` is parameterised by the digits the signatures reveal and the FORS
positions they disclose. This file supplies the instance, and the two halves are supplied for
quite different reasons.

**The WOTS half does not depend on the run at all.** Each WOTS key of the hypertree signs
exactly one message — the honest node one layer below it — so the digit a signature on that key
discloses is a function of the seeds, not of which messages were requested.
`GraphStakes.honestRevealed` is that digit, and `HonestMessage.signLayers_wots` is what pins it
to the signer. Treating a chain as revealed up to that digit before any signature is issued is
an over-approximation of availability, and the residue reduction is unaffected: it leaves the
forgery holding a value *strictly below* that digit, which is unavailable either way.

**The FORS half is about the signing log, which the cache does not carry — but it determines
it.** Signing a message puts that message's `H_msg` input in the cache, and the digest cached
there is exactly what selects the fourteen FORS positions the signature opens. So "this
position was disclosed" is "some cached message-class input's answer selects it", a function of
the cache alone. The adversary can cache a message-class input without having had it signed, so
this over-approximates the signing log too — and that over-approximation is precisely the
coverage event, which `CoverageTail` charges separately. The fork in
`GraphStakes.forsSecret_signed_or_not_obtainable` is where the two meet.

**What monotonicity this supports, and what it does not.** `signedAt` reads cache *values*, so
it is monotone along growth that preserves entries: a cached answer is never rewritten, and a
position a cached digest selects stays selected. It is **not** monotone along growth of the
cache's domain alone, because that relation permits the answer at an input to change, and a
different answer selects different positions. No sound instance can be, since which positions a
digest opens is not a function of which inputs were asked.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CacheAvailability

open CanonicalGraph

/-! ## Entries that survive

The growth relation this file is monotone along: an entry already in the cache is still there,
with the same answer. It is what a run of the lazy handler actually does, and it is strictly
stronger than the growth of the cache's domain. -/

/-- Every entry of the first cache is still present, with its answer, in the second. -/
def Persists (left right : QueryCache HashSpec) : Prop :=
  ∀ (probe : Bytes) (value : HashOutput), left probe = some value → right probe = some value

theorem Persists.refl (cache : QueryCache HashSpec) : Persists cache cache := fun _ _ h => h

theorem Persists.trans {left middle right : QueryCache HashSpec} (hfirst : Persists left middle)
    (hsecond : Persists middle right) : Persists left right :=
  fun probe value hvalue => hsecond probe value (hfirst probe value hvalue)

/-- **Caching a fresh input keeps every entry.** -/
theorem persists_cacheQuery (cache : QueryCache HashSpec) (input : Bytes)
    (answer : HashOutput) (hfresh : cache input = none) :
    Persists cache (cache.cacheQuery input answer) := by
  intro probe value hvalue
  by_cases heq : probe = input
  · rw [heq, hfresh] at hvalue
    exact absurd hvalue (by simp)
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hvalue

/-! ## The FORS positions a cache discloses

A digest discloses the positions it selects only if the *signer* computed it, and the cache says
whether it did: the signer derives the randomiser before the digest, so the `PRF_msg` entry at
`randomizerInput` is in the cache too, and the digest's randomiser is its truncation. Counting
every cached message-class digest instead would let the adversary pick a randomiser of its own,
query the digest itself, and so declare its own fourteen positions disclosed — which charges
nothing and makes the claim at them unavailable, so neither half of the budget sees it.

The gate this creates is that the adversary can make such an entry by querying at
`randomizerInput SK.prf PK.seed M`, which carries `SK.prf` in the clear. That is a guess at the
PRF seed and is charged as one; it is not a canonical input, so it is charged on a class of its
own. -/

/-- A message input whose randomiser is the one the signer derives for that message, with the
derivation's own query in the cache. -/
def SignerRandomised (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (input : Bytes) : Prop :=
  ∃ (message : Bytes) (prfAnswer : HashOutput),
    cache (Hashing.randomizerInput prfSeed pk.seed message) = some prfAnswer ∧
      input = Hashing.messageInput (Hashing.truncate prfAnswer) pk message

/-- Such an input is a message-class input. -/
theorem isMessageInput_of_signerRandomised (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (input : Bytes)
    (hsigner : SignerRandomised prfSeed pk cache input) :
    CombinedCharge.IsMessageInput pk input := by
  obtain ⟨message, prfAnswer, -, hinput⟩ := hsigner
  exact ⟨Hashing.truncate prfAnswer, message, hinput⟩

/-- **A signer-randomised input stays one.** -/
theorem signerRandomised_mono (prfSeed : Digest) (pk : PublicKey)
    {left right : QueryCache HashSpec} (hgrow : Persists left right) (input : Bytes)
    (hsigner : SignerRandomised prfSeed pk left input) :
    SignerRandomised prfSeed pk right input := by
  obtain ⟨message, prfAnswer, hentry, hinput⟩ := hsigner
  exact ⟨message, prfAnswer, hgrow _ prfAnswer hentry, hinput⟩

set_option maxRecDepth 8000 in
/-- **The randomiser of a signer-randomised input is the one the signer derives.** This is the
hypothesis `CanonicalSignature.eq_signInternal` asks for, and the cache is what supplies it. -/
theorem randomizer_eq_of_signerRandomised (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (randomizer : Digest) (message : Bytes)
    (hsigner : SignerRandomised prfSeed pk cache
      (Hashing.messageInput randomizer pk message)) :
    randomizer =
      @Hashing.randomizer Id Id.instMonad (CacheReplay.replayQuery cache) prfSeed
        pk.seed message := by
  obtain ⟨other, prfAnswer, hentry, hinput⟩ := hsigner
  obtain ⟨hrandomizer, -, hmessage⟩ := Hashing.messageInput_injective hinput
  subst hmessage
  rw [hrandomizer]
  show Hashing.truncate prfAnswer =
    Hashing.truncate (@Hashing.hash Id (CacheReplay.replayQuery cache)
      (Hashing.randomizerInput prfSeed pk.seed message))
  rw [CacheReplay.hash_replayQuery cache _ prfAnswer hentry]

open scoped Classical in
/-- **The FORS positions some cached digest of the signer's own discloses.** -/
noncomputable def signedAt (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (key : ForsKey) : Finset (Fin (forsTrees * 2 ^ forsHeight)) :=
  Finset.univ.filter fun index =>
    ∃ (input : Bytes) (answer : HashOutput), SignerRandomised prfSeed pk cache input ∧
      cache input = some answer ∧ SplitCharged.forsKeyOfDigest answer = key ∧
      ∃ tree : Fin forsTrees,
        GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree = index

theorem mem_signedAt (prfSeed : Digest) (pk : PublicKey) (cache : QueryCache HashSpec)
    (key : ForsKey) (index : Fin (forsTrees * 2 ^ forsHeight)) :
    index ∈ signedAt prfSeed pk cache key ↔
      ∃ (input : Bytes) (answer : HashOutput), SignerRandomised prfSeed pk cache input ∧
        cache input = some answer ∧ SplitCharged.forsKeyOfDigest answer = key ∧
        ∃ tree : Fin forsTrees,
          GraphStakes.forsIndex (MessageDigest.forsIndices answer) tree = index := by
  classical
  rw [signedAt, Finset.mem_filter]
  exact ⟨fun hmem => hmem.2, fun hwitness => ⟨Finset.mem_univ _, hwitness⟩⟩

/-- **A cached digest that selects a position keeps selecting it.** -/
theorem signedAt_mono (prfSeed : Digest) (pk : PublicKey) {left right : QueryCache HashSpec}
    (hgrow : Persists left right) (key : ForsKey) :
    signedAt prfSeed pk left key ⊆ signedAt prfSeed pk right key := by
  intro index hindex
  obtain ⟨input, answer, hsigner, hentry, hkey, witness⟩ :=
    (mem_signedAt prfSeed pk left key index).mp hindex
  exact (mem_signedAt prfSeed pk right key index).mpr
    ⟨input, answer, signerRandomised_mono prfSeed pk hgrow input hsigner,
      hgrow input answer hentry, hkey, witness⟩

attribute [local irreducible] signedAt

/-! ## Availability -/

/-- **The cells a run's own cache makes available**: the chain values the honest digit covers,
and the FORS secrets some cached message digest selects. -/
noncomputable def availableAt (secretSeed prfSeed publicSeed : Digest) (pk : PublicKey)
    [HasQuery HashSpec Id] (cache : QueryCache HashSpec) : Node → Prop :=
  Available (GraphStakes.honestRevealed secretSeed publicSeed) (signedAt prfSeed pk cache)

variable [HasQuery HashSpec Id]

set_option maxRecDepth 8000 in
/-- **A released cell stays released.** -/
theorem availableAt_mono (secretSeed prfSeed publicSeed : Digest) (pk : PublicKey)
    {left right : QueryCache HashSpec} (hgrow : Persists left right) (node : Node)
    (havailable : availableAt secretSeed prfSeed publicSeed pk left node) :
    availableAt secretSeed prfSeed publicSeed pk right node := by
  cases node with
  | secretSeed => exact havailable
  | structural parent =>
    cases parent with
    | wotsPrf key chain => exact havailable
    | wotsHash key chain step => exact havailable
    | forsPrf key index => exact signedAt_mono prfSeed pk hgrow key havailable
    | wotsPk key => exact True.intro
    | tree location height index => exact True.intro
    | forsTree key height index => exact True.intro
    | forsRoots key => exact True.intro

/-- **Availability is closed under the structure**, which is what makes a sensitive query the
first place a run can reach a protected cell. -/
theorem availableAt_closed (secretSeed prfSeed publicSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (parent : StructuralNode)
    (hchildren : ∀ child ∈ parent.children,
      availableAt secretSeed prfSeed publicSeed pk cache child) :
    availableAt secretSeed prfSeed publicSeed pk cache (.structural parent) :=
  available_of_children_available _ _ hchildren

/-- A revealed digit never exceeds `w - 1`, which is all the rate asks of it. -/
theorem availableAt_revealed_le (secretSeed publicSeed : Digest) :
    ∀ (key : WotsKey) (chain : Fin chains),
      GraphStakes.honestRevealed secretSeed publicSeed key chain ≤ w - 1 :=
  GraphStakes.honestRevealed_le secretSeed publicSeed

/-- Availability at this instance is the one the stakes structure is stated against. -/
theorem unavailableAt_eq (secretSeed prfSeed publicSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (index : Node) :
    GraphStakes.unavailableAt (GraphStakes.honestRevealed secretSeed publicSeed)
        (signedAt prfSeed pk) cache index ↔
      ¬ availableAt secretSeed prfSeed publicSeed pk cache index := Iff.rfl

/-! ## The handler keeps its entries

The growth `signedAt` is monotone along is the growth a run of the lazy handler performs: a hash
query either reads the cache, leaving it alone, or writes an input the cache had no entry at. -/

open OpenCache LazyBudget

omit [HasQuery HashSpec Id] in
/-- The hash half of the step, at the clean type. -/
theorem lazyProgram_hash_persists (publicSeed : Digest)
    (available : QueryCache HashSpec → Node → Prop) (table : Cells × Padding) (input : Bytes)
    (state : HandlerState) (step : HashOutput × HandlerState)
    (hstep : step ∈ support
      (((lazyProgram publicSeed available table) (Sum.inr input)).run state)) :
    Persists state.1 step.2.1 := by
  classical
  have hbind : step ∈ support
      (lazyAnswer publicSeed available table input state.1 >>= fun inner =>
        (pure (inner.1, (inner.2, state.2.1 ++ [(input, state.1)], state.2.2 + 1)) :
          ProbComp (HashOutput × HandlerState))) := hstep
  rw [mem_support_bind_iff] at hbind
  obtain ⟨inner, hinner, hpure⟩ := hbind
  rw [support_pure, Set.mem_singleton_iff] at hpure
  rw [show step.2.1 = inner.2 from by rw [hpure]]
  rw [lazyAnswer] at hinner
  cases hcached : state.1 input with
  | some cached =>
    rw [hcached, support_pure, Set.mem_singleton_iff] at hinner
    rw [show inner.2 = state.1 from by rw [hinner]]
    exact Persists.refl _
  | none =>
    rw [hcached] at hinner
    cases hopen : openCache publicSeed (available state.1) table input with
    | some answer =>
      rw [hopen, support_pure, Set.mem_singleton_iff] at hinner
      rw [show inner.2 = state.1.cacheQuery input answer from by rw [hinner]]
      exact persists_cacheQuery state.1 input answer hcached
    | none =>
      rw [hopen, support_map] at hinner
      obtain ⟨answer, -, heq⟩ := hinner
      rw [show inner.2 = state.1.cacheQuery input answer from by rw [← heq]]
      exact persists_cacheQuery state.1 input answer hcached

omit [HasQuery HashSpec Id] in
/-- **A step of the lazy handler keeps every cache entry.** -/
theorem lazyProgram_persists (publicSeed : Digest)
    (available : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (queried : OracleWorld.Domain) (state : HandlerState)
    (step : OracleWorld.Range queried × HandlerState)
    (hstep : step ∈ support (((lazyProgram publicSeed available table) queried).run state)) :
    Persists state.1 step.2.1 := by
  rcases queried with coin | input
  · rw [lazyProgram_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [show step.2 = state from by rw [hpure]]
    exact Persists.refl _
  · exact lazyProgram_hash_persists publicSeed available table input state step hstep

omit [HasQuery HashSpec Id] in
/-- **A run of the lazy handler keeps every cache entry.** -/
theorem lazyProgram_run_persists {α : Type} (publicSeed : Digest)
    (available : QueryCache HashSpec → Node → Prop) (table : Cells × Padding)
    (computation : OracleComp OracleWorld α) :
    ∀ (state : HandlerState) (z : α × HandlerState),
      z ∈ support ((simulateQ (lazyProgram publicSeed available table) computation).run state) →
        Persists state.1 z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [show z.2 = state from by rw [hz]]
    exact Persists.refl _
  | query_bind queried next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    exact Persists.trans
      (lazyProgram_persists publicSeed available table queried state step hstep)
      (ih step.1 step.2 z hrest)

end SlhDsaSecurity.CacheAvailability

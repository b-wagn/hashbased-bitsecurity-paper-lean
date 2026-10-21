import SlhDsaSecurity.Proof.CachedRun
import SlhDsaSecurity.Proof.CanonicalGraph.Correspondence
import SlhDsaSecurity.Proof.CanonicalGraph.Programming
import SlhDsaSecurity.Proof.Correctness.Naturality

/-!
# The honest parties ask nothing new

`WarmedGame.graphWalk` evaluates the whole canonical graph before the adversary runs, leaving
a cache that holds an entry at `CanonicalGraph.canonicalInput` of every structural node and at
nothing else. `CachedRun.run_eq_pure_of_cached` turns that into a statement about an honest
party's run — *provided* every input the party consults is one of those canonical inputs.

This file proves that for key generation. The argument is the mirror image of the one the
verifier entry lemmas make: there, a particular byte input had to be exhibited among those a
computation consults; here, *every* input it consults has to be accounted for. So the first
thing needed is the missing direction of `CacheReplay.QueriesUnder` — an inversion principle
saying a query's probes are its own input and whatever its continuation goes on to consult —
and `Probes` packages the resulting universal statement so that it composes along `>>=`.

With that in place, the walk down key generation follows the same recursion the honest
evaluation itself follows: a WOTS chain step is a `.wotsHash` node, its starting secret a
`.wotsPrf` node, a chain's compression a `.wotsPk` node, and an XMSS node a `.tree` node or a
WOTS public key. At each step the payload is built from values the replay has already
determined, and `CanonicalGraph.value_wotsPosition` and `CanonicalGraph.value_merkleChild`
identify those with the cells of the very nodes whose inputs are being matched.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestProbes

open CacheReplay CanonicalGraph

/-! ## Reading `QueriesUnder` as a universal statement

`CacheReplay.QueriesUnder` was built to *exhibit* an input a computation consults. Bounding
the inputs it consults needs the opposite reading, and the only extra ingredient is the
inversion principle below: a bind on a query consults its own input and nothing beyond what
the continuation consults at the replayed answer. -/

/-- A computation that consults anything is a query bound to a continuation, and what it
consults is that query's input or something the continuation consults. -/
theorem queriesUnder_shape {α : Type} {cache : QueryCache HashSpec}
    {computation : OracleComp HashSpec α} {probe : Bytes}
    (hquery : QueriesUnder cache computation probe) :
    ∃ (input : Bytes) (next : HashOutput → OracleComp HashSpec α),
      computation = query (spec := HashSpec) input >>= next ∧
        (probe = input ∨ QueriesUnder cache (next (replay cache input)) probe) := by
  induction hquery with
  | head input next => exact ⟨input, next, rfl, Or.inl rfl⟩
  | tail input probe next hrest _ => exact ⟨input, next, rfl, Or.inr hrest⟩

/-- A query bound to a continuation determines both. -/
theorem query_bind_injective {α : Type} {left right : Bytes}
    {next next' : HashOutput → OracleComp HashSpec α}
    (hshape : (query (spec := HashSpec) left >>= next) =
      (query (spec := HashSpec) right >>= next')) :
    left = right ∧ next = next' := by
  injection hshape with hinput hnext
  exact ⟨hinput, funext fun answer => congrFun hnext answer⟩

/-- **A query's probes are its input and its continuation's.** -/
theorem queriesUnder_query_bind_cases {α : Type} {cache : QueryCache HashSpec}
    {input probe : Bytes} {next : HashOutput → OracleComp HashSpec α}
    (hquery : QueriesUnder cache (query (spec := HashSpec) input >>= next) probe) :
    probe = input ∨ QueriesUnder cache (next (replay cache input)) probe := by
  obtain ⟨other, continuation, hshape, hcase⟩ := queriesUnder_shape hquery
  obtain ⟨rfl, rfl⟩ := query_bind_injective hshape
  exact hcase

/-- Every input `computation` consults, answered from `cache`, satisfies `predicate`. -/
def Probes (cache : QueryCache HashSpec) {α : Type} (computation : OracleComp HashSpec α)
    (predicate : Bytes → Prop) : Prop :=
  ∀ probe, QueriesUnder cache computation probe → predicate probe

theorem probes_pure {α : Type} (cache : QueryCache HashSpec) (value : α)
    (predicate : Bytes → Prop) : Probes cache (pure value) predicate := by
  intro probe hprobe
  cases hprobe

theorem probes_query_bind {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (replay cache input)) predicate) :
    Probes cache (query (spec := HashSpec) input >>= next) predicate := by
  intro probe hprobe
  rcases queriesUnder_query_bind_cases hprobe with rfl | hrest
  · exact hinput
  · exact hnext probe hrest

/-- **Probes compose along a bind.** The continuation is taken at the value the replay gives
the prefix, which `CacheReplay.run_eq_replay` identifies with the value the oracle run
produced; naming that value separately keeps it in whatever form the caller already has it. -/
theorem probes_bind {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    (predicate : Bytes → Prop) (value : α)
    (hvalue : (simulateQ (replay cache) computation : Id α) = value)
    (hcomputation : Probes cache computation predicate)
    (hnext : Probes cache (next value) predicate) :
    Probes cache (computation >>= next) predicate := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
      rw [pure_bind]
      have hresult : result = value := hvalue
      rw [hresult]
      exact hnext
  | query_bind input continuation ih =>
      rw [bind_assoc]
      refine probes_query_bind cache input _ predicate
        (hcomputation input (QueriesUnder.head input continuation)) ?_
      exact ih (replay cache input) hvalue
        (fun probe hprobe =>
          hcomputation probe (QueriesUnder.tail input probe continuation hprobe))

/-- `probes_bind` with the prefix's value left as the replay computes it. -/
theorem probes_bind_replay {α β : Type} (cache : QueryCache HashSpec)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β)
    (predicate : Bytes → Prop) (hcomputation : Probes cache computation predicate)
    (hnext : Probes cache (next (simulateQ (replay cache) computation)) predicate) :
    Probes cache (computation >>= next) predicate :=
  probes_bind cache computation next predicate _ rfl hcomputation hnext

theorem probes_hash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : HashOutput → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (replay cache input)) predicate) :
    Probes cache (Hashing.hash (m := OracleComp HashSpec) input >>= next) predicate :=
  probes_query_bind cache input next predicate hinput hnext

theorem probes_shortHash {α : Type} (cache : QueryCache HashSpec) (input : Bytes)
    (next : Digest → OracleComp HashSpec α) (predicate : Bytes → Prop)
    (hinput : predicate input)
    (hnext : Probes cache (next (Hashing.truncate (replay cache input))) predicate) :
    Probes cache (Hashing.shortHash (m := OracleComp HashSpec) input >>= next) predicate := by
  rw [show (Hashing.shortHash (m := OracleComp HashSpec) input) >>= next =
      (Hashing.hash (m := OracleComp HashSpec) input) >>=
        (fun answer => next (Hashing.truncate answer)) from by
    simp [Hashing.shortHash]]
  exact probes_hash cache input _ predicate hinput hnext

theorem probes_shortHash_self (cache : QueryCache HashSpec) (input : Bytes)
    (predicate : Bytes → Prop) (hinput : predicate input) :
    Probes cache (Hashing.shortHash (m := OracleComp HashSpec) input) predicate := by
  rw [show (Hashing.shortHash (m := OracleComp HashSpec) input) =
      (Hashing.hash (m := OracleComp HashSpec) input) >>=
        (fun answer => pure (Hashing.truncate answer)) from rfl]
  exact probes_hash cache input _ predicate hinput (probes_pure cache _ predicate)

/-- A tweakable call consults its own byte input and continues at the value the cache gives
it — which is the `Id`-level tweakable call under `CacheReplay.replayQuery`. -/
theorem probes_tweakable {α : Type} (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (next : Digest → OracleComp HashSpec α)
    (predicate : Bytes → Prop)
    (hinput : predicate (Hashing.tweakableInput publicSeed address payload))
    (hnext : Probes cache
      (next (@Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload))
      predicate) :
    Probes cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload >>= next)
      predicate := by
  refine probes_shortHash cache _ next predicate hinput ?_
  rwa [replayFold_step_eq_tweakable]

theorem probes_tweakable_self (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (predicate : Bytes → Prop)
    (hinput : predicate (Hashing.tweakableInput publicSeed address payload)) :
    Probes cache
      (Hashing.tweakable (m := OracleComp HashSpec) publicSeed address payload) predicate :=
  probes_shortHash_self cache _ predicate hinput

theorem probes_sequenceFin {α : Type} (cache : QueryCache HashSpec)
    (predicate : Bytes → Prop) :
    ∀ (size : Nat) (parts : Fin size → OracleComp HashSpec α),
      (∀ index, Probes cache (parts index) predicate) →
        Probes cache (sequenceFin size parts) predicate := by
  intro size
  induction size with
  | zero => intro parts _; exact probes_pure cache _ predicate
  | succ size ih =>
      intro parts hparts
      refine probes_bind_replay cache (parts 0) _ predicate (hparts 0) ?_
      exact probes_bind_replay cache _ _ predicate (ih _ fun index => hparts index.succ)
        (probes_pure cache _ predicate)

/-! ## The canonical inputs of a cache

A probe is accounted for when it is some structural node's own byte input, read at the cells
the cache itself determines. `CanonicalGraph.Programming.full_cache_lookup` then puts it in a
completed walk's cache. -/

/-- The honest cells, as a finished cache computes them. -/
def replayCells (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest) : Cells :=
  @value (replayQuery cache) secretSeed publicSeed

/-- An input is canonical when it is some structural node's own byte input. -/
def Canonical (publicSeed : Digest) (cells : Cells) (probe : Bytes) : Prop :=
  ∃ parent : StructuralNode, probe = canonicalInput publicSeed cells parent

theorem childBytes_singleton (cells : Cells) (child : Node) :
    childBytes cells [child] = bytesBE n (cells child) := by
  simp [childBytes]

theorem childBytes_pair (cells : Cells) (left right : Node) :
    childBytes cells [left, right] = bytesBE n (cells left) ++ bytesBE n (cells right) := by
  simp [childBytes]

/-! ## Replaying the honest algorithms

A hash-only computation's replayed value is the same algorithm at `Id` under
`CacheReplay.replayQuery`, which is what `Correctness.Naturality` proves for an arbitrary
faithful implementation. These are the instances of that at a cache. -/

theorem derive_replay (cache : QueryCache HashSpec) (publicSeed secretSeed : Digest)
    (address : Address) :
    (simulateQ (replay cache)
        (Hashing.derive (m := OracleComp HashSpec) publicSeed secretSeed address) : Id Digest) =
      @Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed address :=
  @Correctness.Naturality.derive_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed secretSeed address

theorem chain_replay (cache : QueryCache HashSpec) (publicSeed : Digest) (address : Address)
    (start steps : Nat) (value : Digest) :
    (simulateQ (replay cache)
        (Wots.chain (m := OracleComp HashSpec) publicSeed address start steps value)
      : Id Digest) =
      @Wots.chain Id _ (replayQuery cache) publicSeed address start steps value :=
  @VerifierNaturality.chain_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) publicSeed address start steps value

theorem merkle_node_replay (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (address : Address) (height index : Nat) :
    (simulateQ (replay cache)
        (Merkle.node (m := OracleComp HashSpec) secretSeed publicSeed address height index)
      : Id Digest) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed address height index :=
  @Correctness.Naturality.merkle_node_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed publicSeed address height index

theorem keygenInternal_replay (cache : QueryCache HashSpec)
    (secretSeed prfSeed publicSeed : Digest) :
    (simulateQ (replay cache)
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      : Id (SecretKey × PublicKey)) =
      @Scheme.keygenInternal Id _ (replayQuery cache) secretSeed prfSeed publicSeed :=
  @Correctness.Naturality.keygenInternal_simulate Id _ _ (replay cache) (replayQuery cache)
    (fun _ => rfl) secretSeed prfSeed publicSeed

/-! ## The WOTS side of key generation -/

/-- The single child of a chain step is the chain value one position below it. -/
theorem children_wotsHash (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1))
    (hstep : step.val < w) :
    (StructuralNode.wotsHash key chain step).children =
      [Node.structural (wotsPosition key chain ⟨step.val, hstep⟩)] := by
  by_cases hzero : step.val = 0 <;>
    simp [StructuralNode.children, wotsPosition, hzero]

/-- The cell at a chain position is the chain run that far from the derived secret. -/
theorem replayCells_wotsPosition (cache : QueryCache HashSpec)
    (secretSeed publicSeed : Digest) (key : WotsKey) (chain : Fin chains) (position : Fin w) :
    replayCells cache secretSeed publicSeed (.structural (wotsPosition key chain position)) =
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 position.val
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address chain)) :=
  @value_wotsPosition (replayQuery cache) secretSeed publicSeed key chain position

theorem canonicalInput_wotsPrf (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.wotsPrf key chain) =
      Hashing.tweakableInput publicSeed (Wots.secretAddress key.address chain)
        (bytesBE n secretSeed) := by
  simp only [canonicalInput,
    show (StructuralNode.wotsPrf key chain).children = [Node.secretSeed] from rfl,
    childBytes_singleton]
  rfl

theorem canonicalInput_wotsHash (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) (step : Fin (w - 1)) (hstep : step.val < w) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.wotsHash key chain step) =
      Hashing.tweakableInput publicSeed
        { key.address with
          chainOrHeight := BitVec.ofNat 32 chain.val
          hashOrIndex := BitVec.ofNat 32 step.val }
        (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 step.val
          (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
            (Wots.secretAddress key.address chain)))) := by
  simp only [canonicalInput, children_wotsHash key chain step hstep, childBytes_singleton,
    replayCells_wotsPosition]
  rfl

theorem canonicalInput_wotsPk (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed) (.wotsPk key) =
      Hashing.tweakableInput publicSeed (Wots.publicKeyAddress key.address)
        (digestArrayBytes fun chain : Fin chains =>
          @Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 (w - 1)
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))) := by
  simp only [canonicalInput,
    show (StructuralNode.wotsPk key).children =
      List.ofFn (fun chain : Fin chains =>
        Node.structural (.wotsHash key chain ⟨w - 2, by decide⟩)) from rfl,
    childBytes_ofFn]
  rfl

/-- **Every step of a WOTS chain consults a canonical input.** -/
theorem probes_chain (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) (chain : Fin chains) :
    ∀ (steps start : Nat), start + steps ≤ w - 1 →
      Probes cache
        (Wots.chain (m := OracleComp HashSpec) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } start steps
          (@Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))))
        (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro steps
  induction steps with
  | zero => intro start _; exact probes_pure cache _ _
  | succ steps ih =>
      intro start hbound
      have hstep : start < w - 1 := by simp only [w, winternitzBits] at *; omega
      have hstart : start < w := by simp only [w, winternitzBits] at *; omega
      refine probes_tweakable cache publicSeed
        { key.address with
          chainOrHeight := BitVec.ofNat 32 chain.val
          hashOrIndex := BitVec.ofNat 32 start }
        (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
          { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
          (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
            (Wots.secretAddress key.address chain)))) _ _ ?_ ?_
      · exact ⟨.wotsHash key chain ⟨start, hstep⟩,
          (canonicalInput_wotsHash cache secretSeed publicSeed key chain ⟨start, hstep⟩
            hstart).symm⟩
      · have hchain : (@Wots.chain Id _ (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 (start + 1)
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain))) =
            @Hashing.tweakable Id _ (replayQuery cache) publicSeed
              { key.address with
                chainOrHeight := BitVec.ofNat 32 chain.val
                hashOrIndex := BitVec.ofNat 32 start }
              (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
                { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
                (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
                  (Wots.secretAddress key.address chain)))) := by
          rw [@Correctness.Wots.chain_add (replayQuery cache) publicSeed
            { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start 1
            (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
              (Wots.secretAddress key.address chain)), Nat.zero_add]
          rfl
        show Probes cache
            (Wots.chain (m := OracleComp HashSpec) publicSeed
              { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } (start + 1) steps
              (@Hashing.tweakable Id _ (replayQuery cache) publicSeed
                { key.address with
                  chainOrHeight := BitVec.ofNat 32 chain.val
                  hashOrIndex := BitVec.ofNat 32 start }
                (bytesBE n (@Wots.chain Id _ (replayQuery cache) publicSeed
                  { key.address with chainOrHeight := BitVec.ofNat 32 chain.val } 0 start
                  (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
                    (Wots.secretAddress key.address chain))))))
            (Canonical publicSeed (replayCells cache secretSeed publicSeed))
        rw [← hchain]
        exact ih (start + 1) (by omega)

/-- **A WOTS public key's queries are all canonical.** -/
theorem probes_wots_publicKey (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (key : WotsKey) :
    Probes cache
      (Wots.publicKey (m := OracleComp HashSpec) secretSeed publicSeed key.address)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  refine probes_bind cache _ _ _
    (fun index : Fin chains =>
      @Wots.chain Id _ (replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 index.val } 0 (w - 1)
        (@Hashing.derive Id _ (replayQuery cache) publicSeed secretSeed
          (Wots.secretAddress key.address index))) ?_ ?_ ?_
  · rw [VerifierNaturality.sequenceFin_simulate]
    simp only [Correctness.sequenceFin_id, simulateQ_bind, derive_replay, chain_replay]
    rfl
  · refine probes_sequenceFin cache _ chains _ ?_
    intro index
    refine probes_tweakable cache publicSeed (Wots.secretAddress key.address index)
      (bytesBE n secretSeed) _ _ ?_ ?_
    · exact ⟨.wotsPrf key index,
        (canonicalInput_wotsPrf cache secretSeed publicSeed key index).symm⟩
    · exact probes_chain cache secretSeed publicSeed key index (w - 1) 0 (by omega)
  · exact probes_tweakable_self cache publicSeed _ _ _
      ⟨.wotsPk key, (canonicalInput_wotsPk cache secretSeed publicSeed key).symm⟩

/-! ## The XMSS side of key generation -/

theorem canonicalInput_tree (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) (height : Fin subtreeHeight)
    (index : Fin (2 ^ (subtreeHeight - (height.val + 1)))) :
    canonicalInput publicSeed (replayCells cache secretSeed publicSeed)
        (.tree tree height index) =
      Hashing.tweakableInput publicSeed
        (Merkle.nodeAddress tree.address (height.val + 1) index.val)
        (bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            height.val (2 * index.val)) ++
          bytesBE n (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address
            height.val (2 * index.val + 1))) := by
  simp only [canonicalInput,
    show (StructuralNode.tree tree height index).children =
      [Node.structural (merkleChild tree height index 0),
        Node.structural (merkleChild tree height index 1)] from rfl,
    childBytes_pair,
    show replayCells cache secretSeed publicSeed
        (.structural (merkleChild tree height index 0)) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height.val
        (2 * index.val + 0) from
      @value_merkleChild (replayQuery cache) secretSeed publicSeed tree height index 0,
    show replayCells cache secretSeed publicSeed
        (.structural (merkleChild tree height index 1)) =
      @Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height.val
        (2 * index.val + 1) from
      @value_merkleChild (replayQuery cache) secretSeed publicSeed tree height index 1,
    Nat.add_zero]
  rfl

/-- **Every node of an XMSS subtree consults only canonical inputs.** -/
theorem probes_merkle_node (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (tree : Tree) :
    ∀ (height : Nat), height ≤ subtreeHeight →
      ∀ index : Fin (2 ^ (subtreeHeight - height)),
      Probes cache
        (Merkle.node (m := OracleComp HashSpec) secretSeed publicSeed tree.address height
          index.val)
        (Canonical publicSeed (replayCells cache secretSeed publicSeed)) := by
  intro height
  induction height with
  | zero =>
      intro _ index
      exact probes_wots_publicKey cache secretSeed publicSeed
        ⟨tree, ⟨index.val, index.isLt⟩⟩
  | succ height ih =>
      intro hheight index
      have hleft : 2 * index.val + 0 < 2 ^ (subtreeHeight - height) := by
        have := child_index_lt subtreeHeight height 1 (by omega)
          ⟨index.val, by simp⟩ 0
        simpa using this
      have hright : 2 * index.val + 1 < 2 ^ (subtreeHeight - height) := by
        have := child_index_lt subtreeHeight height 1 (by omega)
          ⟨index.val, by simp⟩ 1
        simpa using this
      refine probes_bind cache _ _ _
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height
          (2 * index.val))
        (merkle_node_replay cache secretSeed publicSeed tree.address height (2 * index.val))
        (ih (by omega) ⟨2 * index.val, by simpa using hleft⟩) ?_
      refine probes_bind cache _ _ _
        (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed tree.address height
          (2 * index.val + 1))
        (merkle_node_replay cache secretSeed publicSeed tree.address height (2 * index.val + 1))
        (ih (by omega) ⟨2 * index.val + 1, hright⟩) ?_
      refine probes_tweakable_self cache publicSeed _ _ _
        ⟨.tree tree ⟨height, by omega⟩ ⟨index.val, index.isLt⟩, ?_⟩
      rw [canonicalInput_tree]

/-! ## Key generation

Key generation is one XMSS node: the root of the top layer's only subtree. Every input it
consults is therefore canonical. -/

/-- The top subtree, whose root is the public key. -/
def topTree : Tree := ⟨⟨layers - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- **Key generation consults only canonical inputs.** -/
theorem probes_keygenInternal (cache : QueryCache HashSpec)
    (secretSeed prfSeed publicSeed : Digest) :
    Probes cache
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)
      (Canonical publicSeed (replayCells cache secretSeed publicSeed)) :=
  probes_bind cache _ _ _
    (@Merkle.node Id _ (replayQuery cache) secretSeed publicSeed topTree.address
      subtreeHeight 0)
    (merkle_node_replay cache secretSeed publicSeed topTree.address subtreeHeight 0)
    (probes_merkle_node cache secretSeed publicSeed topTree subtreeHeight le_rfl
      ⟨0, by decide⟩)
    (probes_pure cache _ _)

/-! ## In the walk's cache

The walk leaves `CanonicalGraph.Programming.cacheFrom` at the cells its own outputs determine.
Those are the cells the cache itself computes, so the canonical inputs key generation consults
are exactly entries the walk installed — and running key generation from that cache samples
nothing and changes nothing. -/

/-- The cache a completed graph walk leaves behind. -/
noncomputable def warmCache (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) : QueryCache HashSpec :=
  Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secretSeed outputs) outputs
    Programming.order ∅

/-- The walk's cache computes the cells the walk itself produced. -/
theorem replayCells_warmCache (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) :
    replayCells (warmCache publicSeed secretSeed outputs) secretSeed publicSeed =
      Programming.cellsOfOutputs secretSeed outputs :=
  @Programming.value_eq_of_cache_agreement
    (replayQuery (warmCache publicSeed secretSeed outputs)) publicSeed secretSeed outputs
    (fun input output hentry =>
      hash_replayQuery (warmCache publicSeed secretSeed outputs) input output hentry)

/-- **A canonical input is in the walk's cache.** -/
theorem warmCache_ne_none (publicSeed secretSeed : Digest)
    (outputs : Programming.Outputs) (probe : Bytes)
    (hprobe : Canonical publicSeed
      (replayCells (warmCache publicSeed secretSeed outputs) secretSeed publicSeed) probe) :
    warmCache publicSeed secretSeed outputs probe ≠ none := by
  obtain ⟨parent, rfl⟩ := hprobe
  rw [replayCells_warmCache]
  show Programming.cacheFrom publicSeed (Programming.cellsOfOutputs secretSeed outputs) outputs
      Programming.order ∅
      (canonicalInput publicSeed (Programming.cellsOfOutputs secretSeed outputs) parent) ≠ none
  rw [Programming.full_cache_lookup]
  exact Option.some_ne_none _

/-- **Every input key generation consults is in the walk's cache.** -/
theorem keygenInternal_probes_cached (publicSeed secretSeed prfSeed : Digest)
    (outputs : Programming.Outputs) (probe : Bytes)
    (hprobe : QueriesUnder (warmCache publicSeed secretSeed outputs)
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed) probe) :
    warmCache publicSeed secretSeed outputs probe ≠ none :=
  warmCache_ne_none publicSeed secretSeed outputs probe
    (probes_keygenInternal (warmCache publicSeed secretSeed outputs) secretSeed prfSeed
      publicSeed probe hprobe)

/-- **Key generation, run from the walk's cache, is a pure computation.** It returns the keys
the cache already determines and leaves the cache exactly as it found it. -/
theorem run_keygenInternal_eq_pure (publicSeed secretSeed prfSeed : Digest)
    (outputs : Programming.Outputs) :
    (simulateQ randomOracle
        (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed)).run
        (warmCache publicSeed secretSeed outputs) =
      (pure (@Scheme.keygenInternal Id _
          (replayQuery (warmCache publicSeed secretSeed outputs)) secretSeed prfSeed publicSeed,
        warmCache publicSeed secretSeed outputs) :
        ProbComp ((SecretKey × PublicKey) × QueryCache HashSpec)) := by
  rw [CachedRun.run_eq_pure_of_cached _ _
    (keygenInternal_probes_cached publicSeed secretSeed prfSeed outputs), keygenInternal_replay]

end SlhDsaSecurity.HonestProbes

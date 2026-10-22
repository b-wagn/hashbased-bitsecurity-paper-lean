import SlhDsaSecurity.Proof.CanonicalSplit
import SlhDsaSecurity.Proof.CoverageRouted
import SlhDsaSecurity.Proof.CoverageTail
import SlhDsaSecurity.Proof.ClaimedProbes

/-!
# The win's branches, at the two predicates the target names

`Target.target_of_obligations` is written, and it names three predicates on one value: the
walk's seeds and cells, the counted outcome, and the final cache. Everything the charges prove
has to arrive in that shape, so the shape is fixed here first and the extraction is routed into
it — not the other way round. A predicate cut to fit a charge and adapted at the join is how a
mismatch hides until the last step.

`AnswerBad` and `InputBad` are therefore stated as the target reads them, as functions of that
one value alone:

* `AnswerBad` is the answer side: a deviating structural collision at the walk's own cells, or
  the forgery's message digest being covered by the other message-class digests. Both are
  charged against the growth the tail is allowed — the collision by `WarmedCharges`, the
  coverage by `CoverageTail.prob_coverage_tail_le`.
* `InputBad` is the input side: some entry of the record of claims the forgery itself
  determines is a sensitive candidate. The record is `ClaimedProbes.claimedCandidatesOf`, whose
  length is the constant `259`, and that constant is what the target's `q - 512 + 259` pays for.

`cases_of_win_routed` takes `CanonicalSplit.cases_of_win_canonical`'s first two branches there,
and `cases_of_canonical` takes the third as far as routing can take it.

**The third branch crosses the line between the two halves**, which is why it is a fork over
both rather than a residue of one. The forgery holds the honest FORS secret at each of the
fourteen positions its digest selects, and each position is either undisclosed — so the secret
it claims is a sensitive entry of the record, which is `InputBad` — or disclosed. If all
fourteen are disclosed, `CoverageRouted.forgeryDisclosedCovered_or_only_self` forks again: the
forgery's digest is covered by the digests that actually disclose, which is `AnswerBad`, or the
forgery's own input is the only one disclosing them. The witnesses are kept at the disclosing
class rather than weakened to the message class, because only a digest the signer randomised
reveals anything, and the signing limit caps those while nothing caps the others.

That last case is `ReplayForgery`, and it is named rather than assumed away. It is the forgery
that is the signer's own signature on a message whose digest only the forgery's own query
selects — so its randomiser is the signer's, which is what the provenance argument needs and
what strong freshness contradicts. Nothing here decides it; `cases_of_win_three` is the split
with that one case left standing.

The coverage event is stated at a cache entry, and `cached_digest` supplies it: the verifier's
first call is the message digest, so the entry is in the run's own final cache and holds what
the replayed verifier reads.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RoutedSplit

open Security CanonicalGraph CacheReplay Extraction VerifierProbes SplitCharged

/-- What the target's predicates are stated on: the walk's seeds and cells, the counted
outcome, and the cache the run ends with. -/
abbrev Trace : Type :=
  (((Digest × Digest × Digest) × Cells) × (Outcome × Nat)) × QueryCache HashSpec

/-- The public key the walk's seeds generate, read from this run's own cache. -/
def keyOf (x : Trace) : PublicKey :=
  generatedKey x.1.1.1.1 x.1.1.1.2.1 x.1.1.1.2.2 x.2

/-- The counted outcome and the final cache, as the charges read a tail's result. -/
def resultOf (x : Trace) : (Outcome × Nat) × QueryCache HashSpec := (x.1.2, x.2)

/-- **The answer side, at a public key held fixed.** A structural collision that deviates from
the walk's cells, or the forgery's own message digest covered by the digests that disclose —
those the signer randomised, which are the only ones that reveal a FORS secret. The key is a
parameter because the charge needs it fixed before the tail runs: both clauses are charged per
query, and which class a query falls in is decided by the key its bytes name. -/
def AnswerBadAt (pk : PublicKey) (x : Trace) : Prop :=
  StructuralTerm.DeviatingCollision x.1.1.1.2.2 x.1.1.2 (resultOf x) ∨
    CoverageRouted.ForgeryDisclosedCovered x.1.1.1.2.1 pk (resultOf x)

/-- **The answer side**, at the key this run's own cache generates. -/
def AnswerBad (x : Trace) : Prop := AnswerBadAt (keyOf x) x

/-- **The input side.** Some entry of the record of claims the forgery determines is the
canonical input of a node whose staked cell no signature has made available. -/
def InputBad (x : Trace) : Prop :=
  ∃ (message : Bytes) (parsed : Signature),
    x.1.2.1.forgery.message.frame = some message ∧
      Signature.fromBytes? x.1.2.1.forgery.signature = some parsed ∧
        ∃ candidate ∈ @ClaimedProbes.claimedCandidatesOf (replayQuery x.2) x.1.1.1.2.2 x.2
            (keyOf x) message parsed,
          SensitiveQuery.Sensitive (GraphStakes.stakes x.1.1.1.2.2)
            (GraphStakes.unavailableAt
              (@GraphStakes.honestRevealed (replayQuery x.2) x.1.1.1.1 x.1.1.1.2.2)
              (CacheAvailability.signedAt x.1.1.1.2.1 (keyOf x)))
            x.1.1.2 x.2 candidate

/-- The forgery's FORS part and its hypertree are both the ones the signer writes for the
digest it carries. -/
def CanonicalAt (x : Trace) (message : Bytes) (parsed : Signature) : Prop :=
  forsKeyOf x.2 (keyOf x) message parsed =
      honestForsKey x.1.1.1.1 x.1.1.1.2.2 x.2
        (Scheme.forsAddress (digestOf x.2 (keyOf x) message parsed)) ∧
    parsed.fors = @SlhDsaSecurity.Fors.sign Id Id.instMonad (replayQuery x.2)
        (MessageDigest.forsIndices (digestOf x.2 (keyOf x) message parsed))
        x.1.1.1.1 x.1.1.1.2.2
        (Scheme.forsAddress (digestOf x.2 (keyOf x) message parsed)) ∧
      parsed.hypertree = @SlhDsaSecurity.Hypertree.signLayers Id Id.instMonad
        (replayQuery x.2) x.1.1.1.1 x.1.1.1.2.2 layers 0
        (MessageDigest.treeIndex (digestOf x.2 (keyOf x) message parsed)).toNat
        (MessageDigest.leafIndex (digestOf x.2 (keyOf x) message parsed)).toFin
        (honestForsKey x.1.1.1.1 x.1.1.1.2.2 x.2
          (Scheme.forsAddress (digestOf x.2 (keyOf x) message parsed)))

/-- Every cached message-class input whose digest selects one of the forgery's own FORS
positions, at the forgery's own FORS instance, *is* the forgery's own input. -/
def OnlySelfAt (x : Trace) (message : Bytes) (parsed : Signature) : Prop :=
  ∃ tree : MessageDigest.ForsTree, ∀ (input : Bytes) (answer : HashOutput),
    CacheAvailability.SignerRandomised x.1.1.1.2.1 (keyOf x) x.2 input →
      x.2 input = some answer →
        forsKeyOfDigest answer = forsKeyOfDigest (digestOf x.2 (keyOf x) message parsed) →
          (∃ other : MessageDigest.ForsTree,
            GraphStakes.forsIndex (MessageDigest.forsIndices answer) other =
              GraphStakes.forsIndex
                (MessageDigest.forsIndices (digestOf x.2 (keyOf x) message parsed)) tree) →
            input = Hashing.messageInput parsed.randomizer (keyOf x) message

/-- **The branch the provenance argument owns.** -/
def CanonicalForgery (x : Trace) : Prop :=
  ∃ (message : Bytes) (parsed : Signature),
    x.1.2.1.forgery.message.frame = some message ∧
      Signature.fromBytes? x.1.2.1.forgery.signature = some parsed ∧
        CanonicalAt x message parsed

/-- Every one of the fourteen positions the forgery's digest selects is disclosed by some
cached digest of the signer's own. -/
def Disclosed (x : Trace) (message : Bytes) (parsed : Signature) : Prop :=
  ∀ tree : MessageDigest.ForsTree,
    GraphStakes.forsIndex
        (MessageDigest.forsIndices (digestOf x.2 (keyOf x) message parsed)) tree ∈
      CacheAvailability.signedAt x.1.1.1.2.1 (keyOf x) x.2
        (forsKeyOfDigest (digestOf x.2 (keyOf x) message parsed))

/-- **The replay case**, which is the canonical branch with its coverage side closed off: the
forgery is the signer's own signature, its positions are disclosed, and the only disclosing
digest that selects them is the one the forgery itself reads.

`Disclosed` is carried rather than dropped because `OnlySelfAt` is a statement about every
disclosing input and says nothing about there being one. What the replay argument needs is a
disclosing input to apply it to, and that is what this supplies. -/
def ReplayForgery (x : Trace) : Prop :=
  ∃ (message : Bytes) (parsed : Signature),
    x.1.2.1.forgery.message.frame = some message ∧
      Signature.fromBytes? x.1.2.1.forgery.signature = some parsed ∧
        CanonicalAt x message parsed ∧ Disclosed x message parsed ∧
          OnlySelfAt x message parsed

/-! ## The record holds both kinds of claim

The two branches produce candidates of the two shapes the record is built from, so reaching
`InputBad` from either is a membership statement about one list. -/

variable [HasQuery HashSpec Id]

omit [HasQuery HashSpec Id] in
/-- **A claimed WOTS value is an entry of the record.** -/
theorem mem_claimedCandidates_wots (publicSeed : Digest) (forsKey : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : Signature)
    (keyAt : Fin layers → WotsKey) (stepAt : Fin layers → Fin chains → Fin (w - 1))
    (layer : Fin layers) (chain : Fin chains) :
    GraphStakes.inputOf publicSeed
        (GraphStakes.wotsHashNode (keyAt layer) chain (stepAt layer chain))
        ((signature.hypertree layer).wots chain) ∈
      GraphStakes.claimedCandidates publicSeed forsKey indices signature keyAt stepAt := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨layer, List.mem_finRange layer, ?_⟩)
  exact List.mem_map.mpr ⟨chain, List.mem_finRange chain, rfl⟩

omit [HasQuery HashSpec Id] in
/-- **A claimed FORS secret is an entry of the record.** -/
theorem mem_claimedCandidates_fors (publicSeed : Digest) (forsKey : ForsKey)
    (indices : SlhDsaSecurity.Fors.Indices) (signature : Signature)
    (keyAt : Fin layers → WotsKey) (stepAt : Fin layers → Fin chains → Fin (w - 1))
    (tree : Fin forsTrees) :
    GraphStakes.inputOf publicSeed
        (GraphStakes.forsLeafNode forsKey (GraphStakes.forsIndex indices tree))
        ((signature.fors tree).secret) ∈
      GraphStakes.claimedCandidates publicSeed forsKey indices signature keyAt stepAt :=
  List.mem_append_left _ (List.mem_map.mpr ⟨tree, List.mem_finRange tree, rfl⟩)

/-! ## The forgery's own message digest is cached

The coverage event is stated at a cache entry, and the entry is there because the verifier put
it there: the message digest is the verifier's first call, so `CacheReplay.queriesUnder_hash`
reaches it in one step and `cached_of_queriesUnder` turns that into the entry. What the entry
holds is then what the replayed verifier reads, which is `digestOf`. -/

omit [HasQuery HashSpec Id] in
/-- **The verifier consults the forgery's message input.** -/
theorem queriesUnder_verify_message (cache : QueryCache HashSpec) (pk : PublicKey)
    (request : Message) (signature : Bytes) (message : Bytes) (parsed : Signature)
    (hframe : request.frame = some message)
    (hparsed : Signature.fromBytes? signature = some parsed) :
    QueriesUnder cache (Scheme.verify (m := OracleComp HashSpec) pk request signature)
      (Hashing.messageInput parsed.randomizer pk message) := by
  simp only [Scheme.verify, Scheme.verifyInternal, hframe, hparsed]
  exact queriesUnder_hash cache _ _

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

omit [HasQuery HashSpec Id] in
set_option maxHeartbeats 1000000 in
/-- **The forgery's message digest is in the run's own cache**, holding the value the replayed
verifier reads. -/
theorem cached_digest (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (message : Bytes) (parsed : Signature)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed) :
    result.2 (Hashing.messageInput parsed.randomizer
        (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message) =
      some (digestOf result.2 (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
        message parsed) := by
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1))).run walk.2) := hresult
  obtain ⟨keys, keyCache, verifyCache, hkeys, hpersist, hverify⟩ :=
    WarmedSplit.split_afterSeeds adversary walk.1.1 walk.2 result hrun
  rw [WarmedSplit.keygenInternal_liftM, WarmedSplit.run_rom_liftM] at hkeys
  rw [WarmedSplit.verify_liftM, WarmedSplit.run_rom_liftM] at hverify
  have hkeyreplay : keys = @Scheme.keygenInternal Id Id.instMonad (replayQuery result.2)
      walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 :=
    WarmedSplit.keygenInternal_eq_replay_of_subset _ _ _ walk.2 keyCache result.2 keys hkeys
      hpersist
  rw [hkeyreplay] at hverify
  have hcached := cached_of_queriesUnder _ verifyCache result.2 result.1.1.verified _
    (queriesUnder_verify_message result.2 (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
      result.2) result.1.1.forgery.message result.1.1.forgery.signature message parsed hframe
      hparsed) hverify
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
  rw [hanswer]
  exact congrArg some (hash_replayQuery result.2
    (Hashing.messageInput parsed.randomizer
      (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message) answer hanswer).symm

omit [HasQuery HashSpec Id] in
set_option maxHeartbeats 1000000 in
/-- **The canonical branch forks across both halves.** Each of the fourteen positions the
forgery's digest selects is either undisclosed, which makes the secret it claims a sensitive
entry of the record, or disclosed; and if all fourteen are disclosed then either the forgery's
digest is covered by the others, which is the answer side, or the forgery's own input is the
only one disclosing them, which is the replay case. -/
theorem cases_of_canonical (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (message : Bytes) (parsed : Signature)
    (hframe : result.1.1.forgery.message.frame = some message)
    (hparsed : Signature.fromBytes? result.1.1.forgery.signature = some parsed)
    (hcanonical : CanonicalAt ((walk.1, result.1), result.2) message parsed) :
    AnswerBad ((walk.1, result.1), result.2) ∨ InputBad ((walk.1, result.1), result.2) ∨
      ReplayForgery ((walk.1, result.1), result.2) := by
  classical
  by_cases hsigned : ∀ tree : MessageDigest.ForsTree,
      GraphStakes.forsIndex (MessageDigest.forsIndices
          (digestOf result.2 (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2)
            message parsed)) tree ∈
        CacheAvailability.signedAt walk.1.1.2.1
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) result.2
          (forsKeyOfDigest (digestOf result.2
            (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
  · rcases CoverageRouted.forgeryDisclosedCovered_or_only_self walk.1.1.2.1
        (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) result message parsed _
        hframe hparsed (cached_digest adversary hresult message parsed hframe hparsed)
        hsigned with hcovered | honly
    · exact Or.inl (Or.inr hcovered)
    · exact Or.inr (Or.inr ⟨message, parsed, hframe, hparsed, hcanonical, hsigned, honly⟩)
  · push Not at hsigned
    obtain ⟨tree, hunsigned⟩ := hsigned
    have hsecrets : ∀ tree : Fin forsTrees, (parsed.fors tree).secret =
        @SlhDsaSecurity.Fors.secret Id Id.instMonad (replayQuery result.2)
          walk.1.1.1 walk.1.1.2.2
          (forsKeyOfDigest (digestOf result.2
            (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed)).address
          (Extraction.Fors.leafIndex (MessageDigest.forsIndices (digestOf result.2
            (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed)) tree) := by
      intro tree
      rw [hcanonical.2.1, @ForsDispatch.sign_apply (replayQuery result.2)]
      rfl
    rcases SplitRouted.signed_or_sensitive_of_secrets walk.1.1.1
        walk.1.1.2.2 (@GraphStakes.honestRevealed (replayQuery result.2) walk.1.1.1 walk.1.1.2.2)
        (CacheAvailability.signedAt walk.1.1.2.1
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2))
        result.2 result.2 walk.1.2
        (WarmedCharges.value_replay_eq_walk_cells adversary hwalk hresult)
        (forsKeyOfDigest (digestOf result.2
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
        (MessageDigest.forsIndices (digestOf result.2
          (generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 result.2) message parsed))
        parsed.fors hsecrets tree with hin | hsensitive
    · exact absurd hin hunsigned
    · exact Or.inr (Or.inl ⟨message, parsed, hframe, hparsed, _,
        mem_claimedCandidates_fors _ _ _ _ _ _ tree, hsensitive⟩)

omit [HasQuery HashSpec Id] in
set_option maxHeartbeats 1000000 in
/-- **A win is the answer side, the input side, or the signer's own signature.** -/
theorem cases_of_win_routed (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hverified : result.1.1.verified = true) :
    AnswerBad ((walk.1, result.1), result.2) ∨ InputBad ((walk.1, result.1), result.2) ∨
      CanonicalForgery ((walk.1, result.1), result.2) := by
  obtain ⟨message, parsed, hframe, hparsed, hcases⟩ :=
    CanonicalSplit.cases_of_win_canonical adversary hresult hverified
  rcases hcases with hdeviating | hresidue | hcanonical
  · exact Or.inl (Or.inl (SplitRouted.deviatingCollision_at_walk_cells adversary hwalk hresult
      hdeviating))
  · refine Or.inr (Or.inl ⟨message, parsed, hframe, hparsed, ?_⟩)
    obtain ⟨layer, chain, hsensitive⟩ :=
      @SplitRouted.sensitive_of_residue (replayQuery result.2) _ walk.1.1.1 walk.1.1.2.2
        (CacheAvailability.signedAt walk.1.1.2.1 (keyOf ((walk.1, result.1), result.2)))
        result.2 walk.1.2
        (WarmedCharges.value_replay_eq_walk_cells adversary hwalk hresult)
        (MessageDigest.treeIndex (digestOf result.2 (keyOf ((walk.1, result.1), result.2))
          message parsed)).toFin
        (MessageDigest.leafIndex (digestOf result.2 (keyOf ((walk.1, result.1), result.2))
          message parsed)).toFin
        parsed (forsKeyOf result.2 (keyOf ((walk.1, result.1), result.2)) message parsed)
        hresidue
    exact ⟨_, mem_claimedCandidates_wots _ _ _ _ _ _ layer chain, hsensitive⟩
  · exact Or.inr (Or.inr ⟨message, parsed, hframe, hparsed, hcanonical⟩)

omit [HasQuery HashSpec Id] in
/-- **A win is the answer side, the input side, or a replay.** This is the split the target's
`hsplit` is one step from: what the provenance argument owes is the third case alone, where the
forgery is the signer's own signature and the only digest disclosing its positions is the one
the forgery itself reads — so the randomiser it carries is the signer's, and strong freshness
is what that contradicts. -/
theorem cases_of_win_three (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support WarmedGame.graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (WarmedGame.tail adversary walk))
    (hwin : Wins .strong result.1.1) :
    AnswerBad ((walk.1, result.1), result.2) ∨ InputBad ((walk.1, result.1), result.2) ∨
      ReplayForgery ((walk.1, result.1), result.2) := by
  rcases cases_of_win_routed adversary hwalk hresult hwin.1 with
    hanswer | hinput | ⟨message, parsed, hframe, hparsed, hcanonical⟩
  · exact Or.inl hanswer
  · exact Or.inr (Or.inl hinput)
  · exact cases_of_canonical adversary hwalk hresult message parsed hframe hparsed hcanonical

end SlhDsaSecurity.RoutedSplit

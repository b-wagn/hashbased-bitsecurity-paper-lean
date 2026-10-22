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

`cases_of_win_routed` takes `CanonicalSplit.cases_of_win_canonical`'s first two branches there.
The third is left standing as `CanonicalForgery`, named rather than assumed away: it is the
forgery whose FORS part and hypertree are both the signer's own, and turning it into a
contradiction with strong freshness is the provenance argument, not a routing step.

**The FORS branch crosses the line between the two halves.** Its disclosed positions are the
coverage event, which `AnswerBad` carries, and its undisclosed ones are sensitive claims, which
`InputBad` carries. That is why the third branch is not simply the input half's problem, and
why the split is written as a fork over both rather than as a residue of one.
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

/-- **The answer side.** A structural collision that deviates from the walk's cells, or the
forgery's own message digest covered by the digests of the other message-class inputs. -/
def AnswerBad (x : Trace) : Prop :=
  StructuralTerm.DeviatingCollision x.1.1.1.2.2 x.1.1.2 (resultOf x) ∨
    CoverageTail.ForgeryCovered (keyOf x) (resultOf x)

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

/-- **The branch the provenance argument owns.** The forgery's FORS part and its hypertree are
both the ones the signer writes for the digest it carries. -/
def CanonicalForgery (x : Trace) : Prop :=
  ∃ (message : Bytes) (parsed : Signature),
    x.1.2.1.forgery.message.frame = some message ∧
      Signature.fromBytes? x.1.2.1.forgery.signature = some parsed ∧
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

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Scheme.sign Security.signingOracle Security.countQueries

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

end SlhDsaSecurity.RoutedSplit

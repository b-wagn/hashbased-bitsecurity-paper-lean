import SlhDsaSecurity.Proof.FinalAssembly
import SlhDsaSecurity.Proof.FramingLeak

/-!
# What the two obligations have to become

`FinalAssembly.target_of_producers` lists the six hypotheses the proof still rests on. Two of
them are not merely unproved, they are **false**, and this file says what replaces them, in
shapes rather than proofs. The two that are false are not false in the same way and do not have
the same repair.

## `hseed` is false, and relocating it would not help

`hseed` bounds `Pr[SplitWitness.SeedRandomised]`. That event says the cache holds an input that
is both message-class at the public key and a `PRF_msg` input at the real seed — and the signer
makes such a query itself. By `FramingLeak.randomizerInput_eq_messageInput`, the request framed
as `PK.root ‖ m` has `PRF_msg(SK.prf, PK.seed, PK.root ‖ m) = H_msg(SK.prf, PK.seed, PK.root, m)`
as *the same byte string*; `FramingLeak.exists_legal_request` says such a request is legal
whenever `PK.root` opens with a zero byte, which `FramingOverlap.keygen_zero_probability` puts at
exactly `1 / 256`. So the event is **certain** on a `1 / 256` slice of key generation, whatever
the adversary's budget. `seedRandomised_of_signer_query` below is that, proved, so the claim is
checkable rather than asserted.

No allowance carries a `2 ^ -8` term. The repair is not to move the charge but to stop making
it: `SeedRandomised` is a blunt over-approximation of what the coverage join actually loses to
the narrowing, and the join needs the narrowed class at exactly **one** input.

## Where the narrowing is really needed, and where it is not

`SplitWitness.Served.cover` asks for `narrow input` to conclude that the input is filed on one
side or the other. For an input the **left** test already keeps, that is more than is needed:
being disclosing is itself a reason to be filed, and the class never enters.
`cover_of_served_or_narrow` below is the weakened form, proved.

With it, the narrowed class is needed only at the **target** — the forgery's own digest input,
which is not disclosing by construction. So the whole leftover is one event: the forgery's
published randomiser is `SK.prf` itself, which is a guess at a secret the adversary never sees.
One unit of `2 ^ -128`, and the answer side's unspent `2 ^ -126` carries it with room to spare.

The witnesses' side of the old leftover — a served request's published randomiser being the seed
— disappears entirely, which matters, because that one is one unit *per served request* and the
signing limit is `2 ^ 64`.

## `hlate` is false, but its charge exists and is already proved

`hlate` says late disclosure never happens on the support. It happens; that is what it is charged
for. But `LateRate.prob_lateDisclosure_le` is a **per-walk** bound, so what sent the charge to the
shared side was never the randomness — it was the count. The count is the target recording's
length, which `LateProbes.probes_le_recordMessageClass` puts inside the record's message-class
part, and `LateProbes.prob_ordering_le` pays it there.

So `¬ Late` becomes a conjunct of the answer side's event and `Late` is paid once on the shared
side. The conjunct has to be expressible, which it is not at `WarmedGame.tail` — a tail result
carries no recordings — so both obligations are read at the fused presentation, where
`FusedCoverage.forgetsTo` carries every event that does not mention the recordings across
unchanged.

## The ledger, and it closes with both allowances unchanged

The answer side's `q / 2 ^ 128` is the two answer charges against one split counter, as before.
The shared side's `(q - 2 ^ subtreeHeight + 259) / 2 ^ 128` is, by `SharedJoin.card_parts_le_budget`,
room for the record's aiming part and its message-class part together, plus the claims. The input
half's bullet turns out to be claims-only, so it spends the `259` and **nothing of the record**.
That leaves both parts free, and the ordering defect needs one of them:

| term | where paid | count |
| --- | --- | --- |
| structural collision | answer | outside slot of the split counter |
| coverage | answer | inside slot of the split counter |
| forgery's randomiser is `SK.prf` | answer | one unit, inside the unspent `2 ^ -126` |
| the forgery's claims | shared | `259` |
| late disclosure | shared | the record's message-class part |
| — | — | the record's aiming part, unspent |

Two units per message-class entry were never needed: the second unit was the witnesses' half of
the seed leftover, and the weakened cover removes it. Neither allowance changes.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ObligationShapes

open Security WarmedGame RoutedSplit Target SplitPrefix

/-! ## The two facts the design rests on -/

/-- **The signer's own `PRF_msg` query makes `SeedRandomised` hold.** On a request framed as
`PK.root ‖ m` the two byte formats coincide, so the signer's randomiser input is a message input
at randomiser `SK.prf` — message-class and `PRF_msg`-class at once, which is the whole event.
This is why the event cannot be charged at any `2 ^ -128` rate: `FramingLeak.exists_legal_request`
makes such a request legal on a `1 / 256` slice of key generation, and on it the adversary makes
the event certain by asking for one signature. -/
theorem seedRandomised_of_signer_query (prfSeed : Digest) (pk : PublicKey)
    (cache : QueryCache HashSpec) (message : Bytes)
    (hcached : cache (Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message)) ≠
      none) :
    SplitWitness.SeedRandomised prfSeed pk cache :=
  ⟨Hashing.randomizerInput prfSeed pk.seed (bytesBE n pk.root ++ message), hcached,
    ⟨prfSeed, message, FramingLeak.randomizerInput_eq_messageInput prfSeed pk message⟩,
    ⟨pk.seed, bytesBE n pk.root ++ message, rfl⟩⟩

/-- **A disclosing input needs no class.** `SplitWitness.Served.cover` asks for the narrowed
class to conclude that an input is filed on one side or the other; an input the left test keeps
is filed for that reason alone. So the class is needed only where the left test fails, which in
the coverage join is the target and nothing else. -/
theorem cover_of_served_or_narrow (narrow : Bytes → Prop)
    (served : Bytes → QueryCache HashSpec → Prop) (input : Bytes)
    (cache : QueryCache HashSpec) (hcover : served input cache ∨ narrow input) :
    served input cache ∨ SplitWitness.Served.targetKeep narrow served input cache := by
  classical
  by_cases hserved : served input cache
  · exact Or.inl hserved
  · exact Or.inr ⟨hcover.resolve_left hserved, hserved⟩

/-! ## The shared half of the new shape is already proved

Nothing in `SharedAssembly`'s argument has to change for it: its proof already splits the shared
event by excluded middle and pays the ordering defect on the far side, so it proves the wider
event as it stands. Only the conclusion was narrower than what the target will need. That the
input half's bullet is claims-only costs nothing here either — a bullet that spends `259` and
none of the record satisfies a hypothesis that allows the aiming part besides. -/

set_option maxHeartbeats 1000000 in
/-- **The shared obligation at its adopted shape, from the same two hypotheses.** -/
theorem sharedChargedLate_of_parts
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary) :
    Obligations.SharedChargedLate FusedCoverage.fusedTail FinalAssembly.forgetFused
      LateProbes.Ordering := by
  classical
  intro q adversary _ hbudget
  have hforget := FusedCoverage.forgetsTo adversary
  have hprobes := LateProbes.probes_le_recordMessageClass hforget
    (FusedCoverage.isRecorderRun adversary)
    (LateProvenance.hrecord_of_signerDigestFree adversary (hsigner adversary))
  have hordering := LateProbes.prob_ordering_le (FusedCoverage.isRecorderRun adversary) hprobes
  refine le_trans (probEvent_mono (q := fun pair : LateProbes.SplitPair =>
    (GoodWalk pair.1 ∧ InputBad (SharedAssembly.splitTraceOf pair) ∧
        ¬ LateProbes.Ordering pair) ∨
      (GoodWalk pair.1 ∧ LateProbes.Ordering pair)) ?_) ?_
  · rintro pair - ⟨hgood, hshared | hordered⟩
    · exact (SharedJoin.cover_of_em
        (fun pair : LateProbes.SplitPair => InputBad (SharedAssembly.splitTraceOf pair))
        LateProbes.Ordering pair hshared).imp (fun hin => ⟨hgood, hin⟩) fun hord => ⟨hgood, hord⟩
    · exact Or.inr ⟨hgood, hordered⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (hinput q adversary hbudget) hordering) ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair => Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair)))
        + ((259 : Nat) : ℝ≥0∞) +
        ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
          (fun pair =>
            Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair)))
      = ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordAiming (LateProbes.forgetRecordings pair))) +
          ClassExpectation.expected (LateProbes.pairedOf FusedCoverage.fusedTail adversary)
            (fun pair =>
              Multiset.card (SharedJoin.recordMessageClass (LateProbes.forgetRecordings pair))) +
          ((259 : Nat) : ℝ≥0∞) := by ring
    _ ≤ ((q - 2 ^ subtreeHeight : Nat) : ℝ≥0∞) + ((259 : Nat) : ℝ≥0∞) :=
        add_le_add (SharedAssembly.expected_parts_le_budget q adversary hbudget) le_rfl
    _ = ((q - 2 ^ subtreeHeight + 259 : Nat) : ℝ≥0∞) := (Nat.cast_add _ _).symm

/-! ## The whole of it, from what is still owed

One hypothesis of the three below is an obligation and two are leaves. The obligation is the
answer half's, restated with late disclosure ruled out; the leaves are the input half's bullet
and the provenance branch the carrier's test retires. Nothing else is assumed. -/

/-- **The target, from the answer obligation and the shared half's two leaves.** -/
theorem target_of_answer_and_leaves
    (hanswer : Obligations.AnswerChargedLate FusedCoverage.fusedTail FinalAssembly.forgetFused
      LateProbes.Ordering)
    (hinput : ∀ (q : Nat) (adversary : Adversary), HasTotalBudget adversary q →
      SharedAssembly.InputBullet adversary LateProbes.Ordering)
    (hsigner : ∀ adversary : Adversary, LateProvenance.SignerDigestFree adversary) :
    HasTotalSecurityBits .strong 127 :=
  FinalAssembly.target_of_producers hanswer (sharedChargedLate_of_parts hinput hsigner)

end SlhDsaSecurity.ObligationShapes

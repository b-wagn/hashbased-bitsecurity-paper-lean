# Before you change this

Short list of facts that are expensive to rediscover and cheap to check first. Each one is a
place where an edit can be *valid* and still wrong, or where a build stays green while a
statement quietly weakens. `PROGRESS.md` has the reasoning; this file has only the checks.

If you are about to change a numeric parameter, a draw, or a recorder, read the matching section
before you edit, not after the build fails.

---

## 1. The concentration margins are 1.09 bits and 0.24 bits

`ForsConcentration`'s two tail bounds end on a division that `norm_num` verifies exactly over
rationals. The slack is not comfortable:

| chain | ratio | needed | slack |
| --- | --- | --- | --- |
| `uniform_load_tail_extended` (main) | `2 ^ -143.09` | `< 2 ^ -142` | 1.09 bits |
| `uniform_load_tail_sharper_of_le` | `2 ^ -127.24` | `< 2 ^ -127` | **0.24 bits** |

**Check `ForsConcentrationSharper.poisson_load_tail_sharper`'s `hscalar` first.** It breaks
before the main chain does, and a quarter of a bit is inside the range that a plausible-looking
parameter change moves things by.

The inputs it is sensitive to: `Statement/Parameters.lean`'s `forsHeight` (12), `forsTrees` (14)
and `totalHeight` (63); the Poisson rate `3` per bin in `ForsConcentration.poissonLoads`; the
`2 ^ 103` and `2 ^ 102` load caps; and the `5 * 2 ^ 62` request cap.

## 2. The `5 * 2 ^ 62` cap is not re-tunable upward

It is the request count the two Chebyshev steps are taken at
(`poisson_count_tail_extended_half`). `2 * signingLimit = 2 ^ 65` is **past the mean** of the
rate-3 Poisson over `2 ^ 63` bins, so there is no larger cap that keeps the tail bound. The cap
reaches the proof as `BlockViews.prob_targetCovered_le`'s `hcap` and is discharged by
`ServedAgreement.record_length_le_cap`.

**`leftLength` and `rightLength` are not symmetric.** The *disclosing* cap buys the `2 ^ -141`
and is the one above. The *target* cap bounds a count only — the charge stays an expectation in
the cells actually read — so a loose `rightLength` costs nothing. Do not "tighten" it.

## 3. Three never-fails are load-bearing, and their failure is silent

`DigestTape.padding_neverFails`, `TapeFactor.splitTapeRun_neverFails` (and
`NoticingTape.noticingSplitTapeRun_neverFails`), `BlockViews.blockRun_tail_neverFails`.

They let `DeferredSampling.evalDist_bind_const_neverFails` drop an unused block and let
`BlockViews.prob_leftBlock` move a block-only event off the run. **If an oracle on one of those
paths gains a failure branch, those equalities become strict rather than unprovable** — the mass
drops below one and nothing in the build says so. Any new handler spliced into a presampled run
owes a never-fails lemma.

## 4. Both recorders try the **left** test first

`RecorderView.recorderOf` (via `appendedOf`'s if-else chain) and `TapeFactor.splitTapeRecorder`
must agree, or an input accepted by both tests lands in different recordings with the same law
everywhere else. The contested case is named:
`TapeFactor.splitRecorder_contested_left` and `TapeFactor.splitTapeRecorder_contested_left`,
both stated with `rightKeep` **present** and both concluding the entry is filed left. If you
change either priority, those are what must still hold.

## 5. The cell correspondences are scoped, on purpose

`TapeFactor.rightOf_getElem?` / `leftOf_getElem?` and their `NoticingTape` counterparts claim
the recording's entry is the block's cell **only where the block still has a cell**. Past the
block the recorder draws for itself and the two part company. That is why
`prob_targetCovered_le` carries `hleftBound` and `hrightBound`; a too-small block length makes
them unprovable rather than fudgeable, which is the intended failure mode.

## 6. Taking disclosures off the whole block is deliberate

`ForsDisclosureTape.disclosures (blockTape length block)` reads cells no query reached. That is
an over-count in the safe direction, and `BlockViews.GoodBlock` is stated at the **same** whole
block, so the load cap and the coverage read one object. Narrowing either to the reached prefix
must narrow both.

## 7. Guards, and what the coverage sweep cannot see

Every new public theorem gets a `#guard_msgs`-guarded `#print axioms` entry in
`Proof/Axioms.lean`, **generated from what the kernel prints, never hand-written**. Expected text
is `[propext, Classical.choice, Quot.sound]` everywhere; anything else is a finding.

The sweep that checks coverage is syntactic: it matches declarations that start a line, behind an
optional attribute or `protected`/`nonrec`, and resolves names through a namespace stack. It is
**blind** to a declaration indented inside a `section` and to one named by a macro. Coverage is
complete as of this writing; if you add either kind, add its guard by hand.

## 8. The leaves are not vacuous, and here is exactly how far that was checked

A leaf that is vacuously true is a silent hole: nothing fails, and the theorem means less than
it reads. Six predicates were probed, each with a satisfiability witness **and** a refutability
witness, and each satisfiability witness paired with a control in which the load-bearing
ingredient is removed. **Every control fails**, so no probe proved less than it looked like.

| predicate | satisfiable | refutable | control fails at |
| --- | --- | --- | --- |
| `AnswerCarrier.carrierRightKeep` | at `framing = none` | `not_carrierRightKeep_randomizerInput` | the left test catching the frame's digest input |
| `SplitWitness.LateDisclosure` | target entry + cached `PRF_msg` | empty target recording | the missing cache entry |
| `AnswerCoverage.ForgerySeedRandomised` | the format identity | unframeable context | a randomiser that is not `SK.prf` |
| `RoutedSplit.InputBad` (and with `GoodWalk`) | empty log + correct claimed cell | unframeable context | `(parsed.fors tree0).secret = base node.child` |
| `CarrierAvailability.availableAt` | `forsRoots` at any carrier | `forsPrf` at the empty carrier | — |
| `GoodWalk ∧ ForgerySeedRandomised` | the format identity at the walk's seeds | — | — |

Three results worth not re-deriving:

**The ordering split is checked, not assumed.** The old trap was a firing predicate false at
every step boundary. The witness has **filing** holding at the step (the flag) and **firing**
holding at the end (the final cache) — two different objects, which is what the three-way
restatement was for.

**`RoutedSplit.InputBad` reads availability from the log** (`ServedLog.disclosedByLog`), **not
from the handler.** The handler decides which *queries* are answered, not which *claims* a
forgery contains, so a handler that refuses unavailable cells cannot empty the event. Reasoning
about the handler here is reasoning about the wrong object.

**The seed leftover cannot be dissolved.** `ForgerySeedRandomised` holds **with certainty** for
a forgery publishing `SK.prf`, through `FramingLeak.randomizerInput_eq_messageInput` rather than
through a collision. No vacuity argument retires it.

### What the probes do **not** establish

**Every witness is free data.** A `Trace`, a result, a carrier state is a tuple, and the probe
chose it. The probes show the *predicates* are non-vacuous; they do **not** show the witnesses
lie in the support of a real run. Nobody has checked reachability of any leaf, and a probe that
did would be a support argument per leaf — a development, not a check.

**The split is non-degenerate as propositions only.** `SigningFaithful.cases_of_win_charged`
gives `Wins → AnswerBad ∨ InputBad`. Both branches were witnessed — a win that is `AnswerBad`
and not `InputBad`, and a win that is `InputBad` and not `AnswerBad` — and **no implication
lemma between the two sides exists anywhere in the tree**, so the split is not degenerate by
construction either. But the two negative halves are bought off-support: `¬ InputBad` with a
context too long to frame (which could not verify) and `¬ AnswerBad` with an empty cache (which
a supported result never has).

**Why that gap was left open deliberately.** A degenerate split would not weaken the theorem:
`HasTotalSecurityBits` bounds `Pr[Wins]` from `Wins → AnswerBad ∨ InputBad` plus a bound on
each, so if every win landed on one side both obligations would still hold and the bound would
be exactly as strong. Degeneracy costs *work*, not strength. And both obligations bound their
own side by something of order `q / 2 ^ 128`, so on the support both sides are rare and
`InputBad ∧ ¬ AnswerBad` is `InputBad` minus a rare set — **degeneracy would need one side to be
unreachable outright, not merely rarer.** Nothing suggests that.

Probes live in the session scratch rather than the repository: they are evidence about the
statements, not part of the proof, and a probe that compiles as a `theorem` is a maintenance
burden with no consumer.

## 9. Standing prohibitions

- Nothing under `SlhDsaSecurity/Statement/` may be redefined. It is the thing being proved.
- No `sorry`, no `admit`, no new axioms.
- `decide +kernel` for closed numerics, **never `native_decide`** — the Stirling table and the
  centered moments are kernel-checked and must stay that way.

## 10. Before claiming an absence

An absence is only established by an exhaustive check. Count first, read second, and when the
conclusion is "nothing anywhere", say how the search was bounded. Two confident negatives in
this development were wrong because a `| head -5` hid the hits.

---

The traps that cost build-days — opaque game definitions, rewriting under binders, the
semireducible index, the projection trap in its three forms, a disjunct that is true outright —
are indexed under **The traps, consolidated** in `PROGRESS.md`.

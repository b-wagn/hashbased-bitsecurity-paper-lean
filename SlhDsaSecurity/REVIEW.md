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

## 8. Standing prohibitions

- Nothing under `SlhDsaSecurity/Statement/` may be redefined. It is the thing being proved.
- No `sorry`, no `admit`, no new axioms.
- `decide +kernel` for closed numerics, **never `native_decide`** — the Stirling table and the
  centered moments are kernel-checked and must stay that way.

## 9. Before claiming an absence

An absence is only established by an exhaustive check. Count first, read second, and when the
conclusion is "nothing anywhere", say how the search was bounded. Two confident negatives in
this development were wrong because a `| head -5` hid the hits.

---

The traps that cost build-days — opaque game definitions, rewriting under binders, the
semireducible index, the projection trap in its three forms, a disjunct that is true outright —
are indexed under **The traps, consolidated** in `PROGRESS.md`.

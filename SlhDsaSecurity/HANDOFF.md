# Continue this: prove 127 bits, or exhibit an attack

## The goal, unchanged

`SlhDsaSecurity.Security.HasTotalSecurityBits .strong 127` — kernel-checked, no `sorry`,
no `admit`, no `native_decide`, no new axioms, `lake build` green, every public theorem
carrying a `#guard_msgs`-guarded `#print axioms` entry in `SlhDsaSecurity/Proof/Axioms.lean`.

`HasTotalBudget` charges **every** hash call in the game — key generation, signing, the
adversary's, and verification — and caps signing requests separately. That is the point of the
exercise: every query in the game is counted. Do not drift onto `HasBudget`/`HasSecurityBits`,
the verifier-counted pair twenty lines above it in `Statement/Security.lean`.

**126 is not a deliverable.** The user has said so explicitly. Either 127, or an adversary
refuting it.

Nothing under `SlhDsaSecurity/Statement/` may be redefined. FIPS 205 parameters, seed lengths,
address formats, checksum, message processing and deterministic signing are preserved.

## What is already true

* **`Target.target_of_obligations_fused_unit : HasTotalSecurityBits .strong 127`** — the socket
  exists, at `claims = 260`, `defectUnits = 2`. Its `Nat` line is `262 ≤ 512` with **250**
  spare (`Target.unitColumn_line`, `unitColumn_margin`). No doubling anywhere, and **no seed
  column**.
* **The answer half is closed.** `AnswerCarrierBound.answerBound_carrier` is
  `q / 2 ^ 128 + 2 ^ -141` taking only the adversary, its budget, the walk and the walk's two
  facts. Nothing assumed.
* **`hparts` at the single line** — `TargetColumn.expected_three_parts_le_budget_unit`, modulo
  one hypothesis: that the `PRF_msg` part's expectation is below one **in the real order**.
* **The attack bar is a theorem.** `GuessingBar` and `PerQueryBudget`: one charged query is one
  staked guess worth exactly `2 ^ -128` (`SecretGuessCharge.prob_single_guess`, an equality),
  and the target is **exactly two** of those (`Assembly.half_add_half`). A refutation needs an
  adversary converting **more than two staked guesses per query** into forgery probability.

## Why 127 is believed true and the loss is ours

`PerQueryBudget`: per charged query, in units of `2 ^ -129`, guessing a secret costs `2`, a
structural collision `2`, FORS coverage `1` — total `5` against a target of `4`. **But an
adversary must apportion its queries among the avenues**, and the best single avenue is rate
`2`. `PerQueryBudget.split_within_target` is that arithmetic, already proved.

And the attack side is closed from the specification: **`Scheme.verifyInternal` computes its
digest from `signature.randomizer`, a field the forger supplies, and never reads `SK.prf`** — so
the format identity's second reading has no per-query forgery value. One query buys one stake.

**So the factor is our union bound's, not the scheme's.**

## The one live route, and exactly where it stands

The bit is lost to a **seed clause** that exists because the reduction loses the forgery's
digest input on the runs where `FramingLeak.randomizerInput_eq_messageInput` bites
(`TargetColumn.filed_nowhere_at_inflight_randomizer`).

Three obstructions were checked. **Two are not obstructions:**

1. **Provenance holds.** `RandomiserProvenance.mem_forgeryDigestRecord` puts that input in the
   record with no hypotheses — the verifier queries it — so `LateProvenance.hrecord` is fine.
2. **The length bound survives filing on cache hits.** `CoverageCount.rightRecord_length_le_count`
   is bounded by the split counter's **inside slot**, and the counter wraps the computation and
   charges every call, hits included (`SharedJoin.card_record_eq_work` is an *equality*). Its
   docstring describes the recorder, not a constraint the counting imposes.

**The third is the whole question:**

> `BlockViews.prob_targetCovered_le` is indexed by **filings**, because `appendedOf`'s freshness
> guard makes the filed answers a prefix of independent uniform values — that is what
> `TapeFactor`'s `evalDist_recordedRun_eq` says, and it is why `rightLength` is the recording's
> length. Filing on a cache hit breaks it: a hit-filed entry has **no fresh value of its own**.
>
> **But the event does not need the filings.** A hit-filed entry's answer *is* an earlier draw's
> answer, so its badness is that draw's badness — fresh at the moment of the draw. Hence
> `Pr[some filed entry is bad] ≤ Pr[some in-class fresh draw is bad]`, and the right-hand side
> is the same tape argument with the tape **cut at draws**. The count rises from filings to
> draws; both are inside the same inside slot. **Same column, larger count.**

**Check this first, before writing anything:** are the in-class *draws* jointly uniform? Filed
answers are, because filing implies freshness. Draws in the class include the **signer's own
queries**, whose inputs come from secrets rather than from the adversary, and `TapeFactor`'s
construction may depend on inputs being adversary-chosen.

* If they are — re-index the tape from filings to draws, let the target recording file on cache
  hits, and the seed clause retires. **127 closes.**
* If they are not — the necessity is real, and the theorem is *the reduction cannot keep the
  object without re-attributing the charge from the filing to the draw, and the factorisation is
  indexed by filings*. That is the statement that explains the bit.

And the ledger-side caution: **if filing on a hit widens the set the rate is charged over, the
coverage charge's per-entry premise moves.** The carrier's served-set repair worked because it
widened the served set *without* widening the thing counted; the same separation has to hold
here, or the repair buys the join at the cost of the rate.

## Also open, and needed either way

* **The game hop** (`SeedFlag`, `SplitSeedView`, `ForgetsOn`) — everything `prob_bad_eq` asks
  for is in hand except `noticingRecorderOf_step_congr`'s `inr` case, the lift through the
  counter, `forgetsLawOn_of_step`, and then carrying
  `RandomiserDeferral.prob_record_meets_prfClass_le` through. **The seed charge is blind-order
  until that lands**; its real-order form is what `hparts` is waiting on.
* **`hinput`** — `ProbeContainment`, one hypothesis from the crossing: the run-level form of
  `ServingTable.probEvent_rom_eq_serving` as a `ForgetsAlong`.

## How to work

Everything below has been paid for in rounds. `SlhDsaSecurity/PROGRESS.md` has the long form.

* **Check, do not assume.** "I did not find X" is a statement about your search, never "X is not
  there" — and a negative result about this codebase has a shelf life.
* **Read the proof, not only the statement.** Twice the missing lemma was a line inside another
  proof, and twice a docstring described the code rather than constraining it.
* **When a quantity is a sum, price the terms before bounding the sum.** Three factors were lost
  today by bounding too early, and all three came back by writing the quantity out.
* **Ask which column a `Nat` is added in** — the constant column caps at `2 ^ subtreeHeight`,
  absolutely, never relative to `q`.
* **State a lemma where its consumer reads it**, and build the socket before the piece.
* **Say which order a probabilistic claim holds in** — blind or real — and do not say "real"
  until the hop has actually been applied.

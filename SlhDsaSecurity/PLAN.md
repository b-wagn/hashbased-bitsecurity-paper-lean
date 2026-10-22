# The plan: close 126 completely

## The arithmetic, once, so nobody re-derives it

Target `HasTotalSecurityBits .strong 127` is `totalAdvantage ≤ q / 2 ^ 127 = 2q / 2 ^ 128`.
Two `q`-columns, no more (`Target.lean:45`).

| clause | count it is charged at | columns |
| --- | --- | --- |
| answer half (coverage + structural) | the target recording | 1 |
| input bullet | `recordAiming` | shares the record |
| ordering | `recordMessageClass` | shares the record |
| seed | the **whole record** — `Pr[seed] ≈ q/2^128` is irreducible | 1 |

Aiming and message-class are **disjoint**, so those two share one record. The seed clause
cannot: its probability is `q/2^128` — guessing a 128-bit secret with `q` queries — so its
count must be record-sized. Three `q`-columns against two: factor `3/2`, i.e. **126**.

**127 therefore needs a reduction with fewer than three `q`-shaped clauses, not a tighter
bound on any of them.** That is a different proof, not a sharper one.

## The four items between here and a hypothesis-free 126

| | item | holder |
| --- | --- | --- |
| A | instantiate `hsplit` into `AnswerCarrierBound.answerBound_carrier` | the carrier-split thread |
| B | the game hop: `prob_bad_eq`, then carry the blind charge across | the randomiser thread |
| C | `hinput` — the counter identification, the honest-chain crossing, then the restatement | the input-half thread |
| D | assemble A, B, C into `Target.target_of_obligations_doubled`'s three hypotheses | the ledger thread |

`target_of_obligations_doubled` is already a theorem. D closes it to a statement with no
hypotheses at all.

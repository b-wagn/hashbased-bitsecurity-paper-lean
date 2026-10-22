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
count must be record-sized, whatever the counts' disjointness. That is what makes our bound
`3q/2^128` rather than `2q/2^128`, i.e. **126**.

**The `3/2` is this reduction's loss, not the loss.** `Proof/PerQueryBudget.lean` counts the
same thing from first principles and gets `5/4`: input-side rate `2` plus answer-side rate `3`
against a target of `4`. More importantly it records that **no adversary attains either** — a
query must be apportioned among the avenues, and the best single avenue is rate `2`, half the
target. So **127 is not refuted**; what fails is a per-query union bound over avenues available
to the same query.

**127 therefore needs an accounting that does not union-bound over avenues** — the bridge named
in `PerQueryBudget`, that a query spent guessing a secret is not simultaneously buying a
structural preimage. `SharedOracleArithmetic.split_within_target` is that arithmetic already;
what is missing is the bridge from the game to an apportionment. That is a different proof, not
a sharper one.

## The four items between here and a hypothesis-free 126

| | item | holder |
| --- | --- | --- |
| A | instantiate `hsplit` into `AnswerCarrierBound.answerBound_carrier` | the carrier-split thread |
| B | the game hop: `prob_bad_eq`, then carry the blind charge across | the randomiser thread |
| C | `hinput` — the counter identification, the honest-chain crossing, then the restatement | the input-half thread |
| D | assemble A, B, C into `Target.target_of_obligations_doubled`'s three hypotheses | the ledger thread |

`target_of_obligations_doubled` is already a theorem. D closes it to a statement with no
hypotheses at all.

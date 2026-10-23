# The shared half at `127`: design

Goal (`AnswerFired.target_of_shared`'s hypothesis): for every adversary with
`HasTotalBudget adversary q`,

    Pr[GoodWalk ∧ (InputBad ∨ Late) | recordedPairedRun adversary] ≤ (q - 512 + 259) / 2^128.

The answer half is closed; this is the only thing left between the repository and
`HasTotalSecurityBits .strong 127`.

## Why the existing input-half pipeline cannot be finished as it stands

* Its charges (`RedrawCell`, `HandlerCharge`, `ChargedHalf`) bound a weight on the support of a
  **blind** run. After the bad event the blind run's answers can be inconsistent with the real
  game, so an adversary that notices may exceed its real-game budget there: `HasTotalBudget` is a
  probability-one statement about the real run only. Nothing caps the adversary.
* `ChargedHalf` runs the **honest** signer through the strict handler. The honest signer queries
  `PRF(SK.seed, ADRS)` inputs, whose staked cell is the secret seed and never available, so the
  `SensitiveAtSeed` term it leaves standing has probability one.
* There is no `SK.prf` hop, and real-order guess charges are false (adaptive stopping), so the
  `SK.prf` guesses and the cell guesses must be counted in **one** game blind to both.

## The route

1. **Cap the adversary** (`capComp`): truncate its computation once its weighted queries — one per
   hash call, one per framed signing request — would exceed `L := q - 36 · 512`. On the real game
   the cap never fires (`work + keygen + 2 · served ≤ q`, keygen `≥ 36 · 512`), so the event's
   probability is unchanged; on every game the capped adversary's weighted queries are `≤ L`.
2. **A handler presentation of the real game** (`H_R` over one computation `C`): the adversary
   phase with each signing request split into two queries — *draw* (the `PRF_msg` and `H_msg`
   queries, which file the request so its FORS secrets become available) and *assemble* (the
   signature, read off the cell table: `CanonicalGraph.Correspondence` says the honest signer's
   output under the warm cache is a function of the cells). Equal in law to `recordedPairedRun`.
3. **The blind handler** `H_B` on the same `C`: the oracle is `OpenCache.lazyProgram`-style
   (canonical inputs answered from the table only at nodes whose children are available), and the
   signer's `PRF_msg` answer comes from a fresh frame-keyed table instead of the oracle. `H_R` and
   `H_B` are identical until `Bad := sensitive adversary/verifier probe ∨ PrfHit ∨ SignerHit`
   (VCVio's `probEvent_output_bad_eq'` and the event-off-the-flag transfer).
4. **The union bound in `H_B`**: `SK.prf` is never read, the frame table is independent of it,
   and each unavailable cell (secret seed included) is redrawable until it becomes available
   (stall + redraw). Every guess costs `2 ^ -128`; the guesses are the record's aiming part, its
   `PRF_msg` candidates, the framed signing requests, and the forgery's `259` claims. With the cap
   and `VerifyBound.isQueryBoundP_verify` (`≤ 3929` verifier calls) that is
   `L + 3929 + 259 ≤ q - 512 + 259`.

## Status

Done: `SlhDsaSecurity.ShareFinal.hasTotalSecurityBits_strong_127 :
HasTotalSecurityBits .strong 127`, axioms `propext, Classical.choice, Quot.sound`.

| Step | Where |
| --- | --- |
| Verifier makes at most `3929` hash calls | `VerifyBound` |
| Key generation spends at least `36 · 512`; the budget pays for it | `KeygenCost`, `ShareFinal.keygen_le_of_budget` |
| The cap and its transparency on the real side | `CapComp`, `ShareRealCap` |
| One computation, lenient and blind handlers, one sticky flag | `ShareGame` (availability read off the table: `ShareCells`) |
| Identical until the flag | `ShareUntilBad` |
| Flag witnessed by the record; record length is the cap's weight | `ShareFlag` |
| Stall-and-redraw charge at any spec and state | `BlindCharge` |
| The blind step reads only released cells | `ShareBlindFacts`, `ShareSignCongr` |
| Blind flag `≤ (L + 3929 + 259) / 2^128` | `ShareBound.blind_bound` |
| Real game flattened to one handler per phase | `SharePresent` |
| Real and lenient games coupled | `ShareCouple`, `ShareInv`, `ShareWhole` |
| The real event raises the lenient flag | `ShareClaims`, `ShareEvent` |
| Averaging and the statement | `ShareFinal` |

Design changes made along the way: the signer's digest input is filed (so its coincidence is one
more record guess), assembly answers only at a drawn digest (so every step of the blind handler is
blind, not only those the computation makes), and availability uses the table's own signed cells
rather than the replayed `honestRevealed` (which is defined at keys outside the hypertree, where
blindness would need every replayed lookup to miss).

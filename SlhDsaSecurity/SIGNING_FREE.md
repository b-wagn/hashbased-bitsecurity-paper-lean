# Signing-free 127 bits: proof plan and obstruction

Target: `HasLimitedSecurityBits .strong {hash, verifier} 127` — the adversary's signing
requests free, the `2^64` signing limit kept. Proved today: `slhDsa_sufCma_127` at
`adversaryWork = {sign, hash, verifier}`. Units below: `u = 2^-128`; the target is `2q` units.

## Where a request is charged today

1. **Answer half** (`BySourceAnswer.fresh_add_right_le`):
   `freshMass (Deviating ∨ Targeted) ≤ |record| + |requests|`. The `+ |requests|` is
   bookkeeping only. A request's fresh entries are canonical, its `PRF_msg` input, and its digest
   input. None of them is `Deviating`, and the digest is filed on the *left* (disclosing), not
   the right. So `freshDev + |right| ≤ |record|` should hold pathwise. **Removable; a few days.**
2. **Shared half** (`ShareGame.weight`, one unit per framed request): the blind game, with
   `SK.prf` drawn at the end, flags `SignerHit` (some randomiser `R_i = SK.prf`). That is
   `S·u ≤ 2^-64` in total, against roughly `2u` of fixed slack. **This is the real charge.**

## Why `SignerHit` cannot just be dropped

`SignerHit` alone is harmless. It matters through the **link**: on keys with
`PK.root[0] = 0x00` (probability exactly `1/256`), a free request framed `PK.root ‖ f_i` is
served with `R_j = trunc(digest_i)` (`FramingLeak.randomizerInput_eq_messageInput`). A blind
game cannot reproduce that, so it must flag it, which costs `S·u`.

The ledger has no room for an absolute term of `2^-72`:

* a structural query costs exactly `2u` (answer fault `u` plus aiming `u`), both genuine;
* only message-class and `PRF_msg`-shaped queries carry spare charge (the coverage term is
  `2^-129` per target, against `u` budgeted), and they carry at least `¼u`.

## The decomposition that almost works

`late := PrfHit ∨ SignerHit`, and `win ⇒ ¬Good ∨ answerFault ∨ aim ∨ (coverage ∧ ¬late) ∨
(PrfHit ∧ ¬SH) ∨ (SH ∧ coverage)`.

* `(PrfHit ∧ ¬SH)` in real order. On `s ∉ {R_i}` the run with `SK.prf = s` is the no-link run,
  so `Pr ≤ u·E[cand]·(1 + (q+S)u)`. The excess `(q+S)u` is at most `¼` for `q ≤ 2^126`, and is
  paid from the candidates' spare charge.
* `(SH ∧ coverage)` *without* `PrfHit`. Only the one link-derived randomiser can fire
  adaptively. A crude coverage bound (`d` signed digests in `inst(c)`, giving `(d/4096)^14`
  with a binomial tail for `d`) gives `β ≤ 2^-66` per target. So `Σ_i Pr[R_i = SK.prf ∧ c covered]
  ≤ S·u·β ≤ ¼u` per target, paid from the targets' spare charge.
* **Cross-half transfer needs one probability space.** Caps (`max` over paths) cannot move
  per-query slack from the answer half to the shared half. The aiming charge must stay blind:
  real order has the adaptive-stopping excess `q²u²`, which a structural query cannot pay. So
  the aiming charge and the `PrfHit` charge must be counted in one game. The game that works
  is real except for blind cells, keeping `SK.prf` and the signer real; `Pr[aim] ≤ u·E[loc]`
  holds there. The `PrfHit` count before the first aim equals the real one, so its excess
  transfers. This means restructuring `ShareGame`, whose blind handler uses a frame-keyed
  randomiser table and `SK.prf` drawn at the end.

## The obstruction: `SH ∧ PrfHit` via a one-query detection probe

On a root-valid key with the pair `(i, j)` requested, the adversary knows `R_j`, which is
`trunc(digest_i)` if `R_i = SK.prf`. **One structural probe** detects the link: hash sig_i's
revealed FORS secret of tree 1 at leaf address `(I(i), 1, x_1(R_j))`. The probe hits an honest
entry iff the link holds (up to `2^-12`). After detection, `SK.prf = R_i` is public, and the
`2^78`-query grinding attack applies.

* On non-link paths the probe is fresh, and its `2u` charge is genuine.
* On link paths it is a hit, and detection succeeds.

So per probe, `Pr[fault ∨ detect] ≈ 2u + 2^-136 ≈ 2u + 2^-8 u`. **Every per-query union-bound
ledger of this shape is exceeded** unless the probe's cost is found elsewhere.

**This is not an attack.** A FORS-leaf fault does not convert into a forgery, and winning after
detection still needs about `2^78` queries. The real advantage stays far below `q/2^127`.

## What a proof needs (research-level)

Either one of these:

1. **Position hiding plus hit slack.** To name `I(i)`, the instance address (63 bits taken from
   `digest_i` past `R_j`), the adversary has to verify hypertree layers. The correct guesses
   are **non-fresh hits**, hundreds per WOTS verification, and their answer-half charge goes
   unused. That is far more than the `≤ 15 · 2^-8 u` of detection value per instance group.
   Formally this needs a relabeling coupling of the random oracle that is identical until a hit:
   * XOR masks on leaf indices at every hypertree layer and in the FORS trees, swapping
     left/right child order on masked bits;
   * the masks XORed into the index bits of digests landing there;
   * the masks kept consistent with every signature.

   It also needs crediting non-fresh hits in both halves.
2. **FORS faults charged jointly with coverage.** A FORS-leaf fault only helps a forgery whose
   digest selects that leaf with the other 13 covered. Re-architecting the answer half this way
   frees slack on every FORS-shaped query.

Either is a re-architecture of a large part of the proof, not a lemma added to it.

## Suggested order, if pursued

1. Answer-half bookkeeping without requests (days).
2. One-game shared half: real `SK.prf`, blind cells, expectation form; `PrfHit` charged in
   real order (weeks).
3. Leaked-world crude coverage for `SH ∧ coverage` (about a week).
4. Hiding plus hit slack, or joint FORS charging (months; research risk).

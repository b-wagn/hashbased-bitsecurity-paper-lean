# SLH-DSA-128s: proof status

**Preparatory arithmetic only. The 127-bit security theorem is not established.**

The intended experiment is deterministic, pure SLH-DSA-128s with at most
2^64 signing requests. Work counts direct adversary hash calls and every hash
call in final verification, including repeated inputs. Honest key generation
and signing share the same oracle but contribute no work. The target is
SUF-CMA advantage at most q/2^127 for every almost-sure work budget q ≥ 1;
EUF-CMA should follow from the same experiment.

## Source audit

- [FIPS 205](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf),
  Table 2: n=16, h=63, d=7, h'=9, a=12, k=14, lg(w)=4, m=30.
  Algorithms 7–8 use 32 message digits and three checksum digits, most
  significant first. Algorithm 18 computes only the top XMSS tree.
- [leanVM at 3a37fb6](https://github.com/leanEthereum/leanVM/tree/3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45/formal/lean_sphincs):
  `Sphincs/StatementDet.lean` uses `Statement.countedOracle`, which charges
  **all** hashes. `Scheme.lean` fixes one height-26 tree, 256-bit seeds,
  target-sum WOTS, and a custom forest. `Lifetimes.requestedSecurity` is not
  a theorem about standard SLH-DSA. `BridgeHeavyCert.det_bitsFH` explicitly
  subtracts `keygenCost` from q; its certificates include that credit.
- The existing XMSS `Proof/Checksum/Modes/Verifier.lean` supplies a useful
  accounting pattern: reserve the final verifier's work and prune the
  adversary's direct-query budget. Its cryptographic bound does not cover
  FORS, a hypertree, or the standard 128-bit seeds.

## Model decisions and outstanding obligations

Start with the SHAKE byte formats in FIPS 205 Section 11.1, idealizing SHAKE
as one consistent random oracle. A 30-byte output suffices for all scheme
calls; 16-byte outputs must be prefixes of that same answer. One oracle
call is one unit, independent of input length. This is an ideal-hash claim,
not a concrete SHAKE or SHA2 security proof. The exact game is not implemented
yet.

Preserve the 32-byte addresses, both independent 16-byte secret seeds,
public seed, message processing, and all nine unused bits in the 30-byte
message-digest layout. The PRF address types distinguish WOTS and FORS
derivation. Message randomization and message hashing use their specified
byte concatenations; they cannot be replaced by independently tagged oracles
without a proof that accounts for overlaps.

The security argument still needs a joint adaptive bound for seed guesses,
FORS disclosures and reuse, digest prequeries selected by subsequent signing,
WOTS/hypertree modifications, and the final verification. A fixed, independent
FORS target calculation cannot discharge these obligations. No component
security hypothesis or numerical security certificate has been assumed.

`Proof/Parameters.lean` checks the standard dimensions and signature length.
`Proof/Checksum.lean` proves the WOTS chain-step range 45–510, including both
endpoints. Relating this arithmetic to the oracle trace remains to be done.
All existing XMSS definitions and proofs are unchanged.

## FORS components

`Proof/ForsCoverage.lean` proves the exact coverage probability of an independent
uniform target. If `s_i` bounds the number of disclosures at instance i, the
probability is at most `sum_i s_i^14 / 2^231`. In particular, the deterministic
condition `sum_i s_i^14 <= 2^103` suffices for a bound of 2^-128. This result
does not assert that an adaptive signing transcript satisfies the condition.

`Proof/ForsMoments.lean` checks Touchard-polynomial values through degree 84
and a sixth-moment scalar inequality. The following concentration route still
needs its probabilistic proof. Write B=2^63 and first consider 2B independent
uniform instance selections. Poissonizing to independent loads of mean 3
would dominate this experiment with a factor at most 2: the total has mean
3B and variance 3B, so Chebyshev bounds the probability of fewer than 2B
selections by 3/B. For Y equal to one load raised to power 14, the checked
polynomials bound its moments through order six. Centering Y and expanding
the sixth moment of the sum leads to the four terms in
`sixth_moment_scalar`, bounded by 2^-142 at threshold B*2^40. The resulting
candidate load-tail bound is 2^-141. Neither the moment identities nor this
coupling have yet been formalized here.

Even after that step, the ROM proof must handle signing whose digest was
queried in advance, future disclosures, and overlaps between the specified
SHAKE inputs. For example, at the internal-message level, H_msg with R=SK.prf
has the same input as PRF_msg on PK.root concatenated with that message.
The pure-message encoding also matters when analyzing such overlaps.
A hybrid that simply declares these roles independent is insufficient.

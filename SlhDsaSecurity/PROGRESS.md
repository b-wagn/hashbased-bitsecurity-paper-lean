# SLH-DSA-128s: proof status

**Concrete construction and experiment. The 127-bit security theorem is not established.**

The experiment is deterministic, pure SLH-DSA-128s with at most
2^64 signing requests. Work counts direct adversary hash calls and every hash
call in final verification, including repeated inputs. Honest key generation
and signing share the same oracle but contribute no work. The target is
SUF-CMA advantage at most q/2^127 for every almost-sure work budget q ≥ 1;
`Proof/Security.lean` proves that any SUF-CMA bound implies the same EUF-CMA bound.

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
not a concrete SHAKE or SHA2 security proof.

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
endpoints. `Proof/VerificationQueries.lean` connects this arithmetic to every
verifier trace: WOTS verification uses 46–511 calls, FORS uses exactly 183,
and a parsed signature with a valid message frame uses 569–3824 calls.
These bounds survive any stateful oracle implementation and initial cache;
repeated inputs are charged. Connecting the instrumentation directly to the
experiment's `Outcome.counts` remains to be done.
All existing XMSS definitions and proofs are unchanged.

`Statement/{Types,Address,Hashing}.lean` now defines the standard key fields,
32-byte addresses, SHAKE input concatenations, shared 30-byte oracle, short-output
truncation, and pure-message framing. `Proof/Hashing.lean` proves injectivity of
the byte serialization, addresses, each hash-input format, and successful framing.
Different structural address types give different inputs. The exact overlap
between message hashing and message randomization is also proved; it is not an
attack or a claim that the security target is impossible.

`Statement/{Wots,Merkle,Fors,Hypertree,Scheme}.lean` defines the complete
deterministic algorithms, including on-demand secret derivation and key generation
of only the top tree. `Statement/Signature.lean` supplies the standard byte layout
and decoder. `Statement/Security.lean` defines the adaptive experiment and the
exact target proposition `HasSecurityBits .strong 127`. Every request counts,
including repetitions and rejected contexts; honest hashes are uncharged and
every direct or final-verifier hash call is charged. The lifetime and work bounds
hold jointly with probability one. `Proof/{Signature,SignatureCanonical}.lean`
proves both codec roundtrips, including that every accepted byte string is the
canonical encoding of its parsed value. Algorithm correctness still requires
proofs.

## FORS components

`Proof/ForsCoverage.lean` proves the exact coverage probability of an independent
uniform target. If `s_i` bounds the number of disclosures at instance i, the
probability is at most `sum_i s_i^14 / 2^231`. In particular, the deterministic
condition `sum_i s_i^14 <= 2^103` suffices for a bound of 2^-128. This result
does not assert that an adaptive signing transcript satisfies the condition.

`Statement/MessageDigest.lean` implements the standard 21/7/2-byte split.
`Proof/MessageDigest.lean` proves joint uniformity of its 63-bit instance and
fourteen 12-bit FORS indices when the full 240-bit answer is fresh and uniform.
The proof retains the nine ignored bits to obtain a bijection; they have not
been removed from the hash output. `fresh_digest_coverage` connects this parser
to the exact coverage count. Freshness of an adaptively selected input remains
a separate obligation.

`Proof/ForsMoments.lean` checks Touchard-polynomial values through degree 84.
`Proof/ForsConcentrationPoisson.lean` identifies them with moments of the actual
Poisson measure and proves integrability and centered moments. Using the exact
sixth moment of a sum of independent variables, `Proof/ForsConcentration.lean`
proves that 2^63 independent Poisson(3) loads satisfy
`Pr[sum_i load_i^14 >= 2^103] <= 2^-142`.

`Proof/ForsConcentrationOccupancy.lean` proves the exact multinomial occupancy
law and its Poisson mixture, preserving the dependencies between bins. Monotonicity
and a second-moment bound transfer the Poisson result to every fixed N ≤ 2^64
independent uniform instance selections:
`Pr[sum_i load_i^14 > 2^103] <= 2^-141`.
The adaptive signing transcript remains a separate argument.

Even after that step, the ROM proof must handle signing whose digest was
queried in advance, future disclosures, and overlaps between the specified
SHAKE inputs. For example, at the internal-message level, H_msg with R=SK.prf
has the same input as PRF_msg on PK.root concatenated with that message.
The pure-message encoding also matters when analyzing such overlaps.
A hybrid that simply declares these roles independent is insufficient.

`Proof/HashSeparation.lean` proves a separation criterion for H_msg versus
structural hashing: an overlap requires PK.seed concatenated with PK.root to
encode the structural address. A loose rectangle enclosing the standard
128s address ranges has at most 2^91 candidates, so an independently uniform
pair of 16-byte values satisfies this condition with probability at most
2^-165. `Proof/{KeygenFresh,KeygenUniform}.lean` proves that the actual top-tree
root is a fresh uniform output, and that actual key generation yields independent
uniform public seed and root. Thus the 2^-165 bound now applies directly to
key generation. The address ranges still need to be connected to all algorithm
traces. PRF_msg versus structural hashing is also proved disjoint whenever
SK.prf differs from PK.seed. These results do not resolve the remaining
H_msg/PRF_msg overlap.

`Proof/PartialDigest.lean` proves that fixing the first 128 output bits leaves
the instance and final three FORS indices jointly uniform in the remaining
112 bits. For fixed disclosures with at most L leaves per tree and a fixed set
of instances, coverage is at most `|instances| * L^3 / 2^99`; at L=256 this is
`|instances| / 2^75`. Applying it to adaptive disclosures requires a freshness
and independence argument that is not yet proved.

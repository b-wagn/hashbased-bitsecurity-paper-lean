# Security of XMSS in the random-oracle model, in Lean 4

Machine-checked security statements and proofs for the XMSS instance of Ethereum's
post-quantum consensus with the one-time signature replaced by WOTS with a checksum, as in
SLH-DSA (FIPS 205), in Lean 4 using [VCVio](https://github.com/Verified-zkEVM/VCVio).
The development started from the 127-bit SUF-CMA proof in
[leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss) and
separates *what is claimed* from *why it holds*.

The library proves the exact classical bit security of XMSS for **all 16 counting modes**,
under both strong (SUF-CMA) and standard (EUF-CMA) unforgeability. Each classification is one
theorem: `XmssSecurity.xmss_sufCma_exact` in `XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean`
and `XmssSecurity.xmss_eufCma_exact` in `XmssSecurity/Statement/UnforgeabilityTheorems.lean`.
A standard forgery must use an epoch/message pair never requested from the signer,
including requests that returned no signature.

As in the manuscript, each notion has a single experiment that outputs whether the adversary
wins together with five query counts: the adversary's signing queries `q_S` and direct hash
queries `q_H`, and the hash queries of key generation `q_Gen`, of the signer `q_Sig`, and of the
final verification `q_Ver`. A counting mode `Z` is a set of these kinds, and bit security in mode
`Z` measures the adversary's work as the sum of the counts in `Z`. In Lean the kinds are
`SUFCMA.QueryKind.sign`, `.hash`, `.keygen`, `.signer`, and `.verifier`. The theorems cover the
sixteen modes with `q_H ∈ Z`.

| Counting mode `Z` (with `q_H ∈ Z`) | Strong SUF-CMA | Standard EUF-CMA |
|---|---|---|
| `{q_H}`, `{q_H, q_S}` | exactly 122 bits | exactly 122 bits |
| `{q_H, q_Sig}` | exactly 123 bits | exactly 123 bits |
| `{q_H, q_S, q_Sig}` | exactly 124 bits | exactly 124 bits |
| `Z` contains `q_Gen` or `q_Ver` (12 modes) | exactly 127 bits | exactly 127 bits |

The encoding (`Statement/Scheme/Checksum.lean`) reads a 128-bit digest as `len_1 = 43` digits of
`w = 3` bits and appends the `len_2 = 3` base-8 digits of the checksum `Σ (7 - x_i)`, for
`v = 46` chains. Every digest encodes, so the signer makes a single attempt and costs two hash
calls (the randomizer and the encoding).

*Status (work in progress).* Two cases are still open: the budget `q = 1` when the signer's hash
calls are charged, and the budgets `q ≤ 3` when the signer's hash calls and the signing queries
are charged (`Proof/Signer/Security.lean`). Until they are closed, the axiom checks in the two
theorem files fail.

*Disclaimer.* The Lean code proves statements about the scheme as defined in `Statement/Scheme/`,
with the hash function modelled as a random oracle. It does not prove security of any
implementation and cannot replace an audit.



## Theorems

| Theorem | File | Result |
|---|---|---|
| `xmss_sufCma_exact` | `Statement/StrongUnforgeabilityTheorems.lean` | SUF-CMA, every `Z` with `q_H ∈ Z`: exactly 127 bits if `Z` contains `q_Gen` or `q_Ver`, else 124 bits if it contains `q_Sig` and `q_S`, 123 bits if it contains `q_Sig`, and 122 bits otherwise |
| `xmss_eufCma_exact` | `Statement/UnforgeabilityTheorems.lean` | EUF-CMA, the same levels |



The adversary is probabilistic, adaptive, and unbounded in time and memory. Each counting mode
specifies which hash queries and signing queries count as the adversary's work. The probability is over the
master seed, the random oracle, and the adversary's private randomness.

## Building

```
lake exe cache get   # Mathlib cache
lake build          # strong and standard security proofs, attacks, and axiom guards
```

Toolchain: Lean `v4.31.0`; VCVio pinned to `cbd4144` in `lakefile.toml`.

`lake build` builds the single `XmssSecurity` library. Its root module imports both theorem
files, so both classifications, including the matching attacks, are checked in the same build.
To check that the statement layer imports the proof layer only through the theorem files, run
`scripts/check_statement_imports.sh`.

The main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Both theorem files check this with `#guard_msgs`, so the build fails if a `sorry`
or a nonstandard axiom enters.

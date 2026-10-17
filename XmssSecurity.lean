import XmssSecurity.Statement.StrongUnforgeabilityTheorems
import XmssSecurity.Statement.UnforgeabilityTheorems

/-!
# Security of XMSS in the random-oracle model

The public entry point for the `XmssSecurity` library. Importing this module checks the exact
classifications of strong (SUF-CMA) and standard (EUF-CMA) unforgeability, under all sixteen
counting modes that charge the adversary's own hash queries, of XMSS with two WOTS encodings:

* `xmssTargetSum_sufCma_exact` and `xmssChecksum_sufCma_exact`
  (`Statement/StrongUnforgeabilityTheorems.lean`);
* `xmssTargetSum_eufCma_exact` and `xmssChecksum_eufCma_exact`
  (`Statement/UnforgeabilityTheorems.lean`).

With the target-sum encoding: exactly 127 bits when any honest party's hashes are charged, and
otherwise 122 bits (SUF-CMA), or 126 bits for `{hash}` and 127 bits for `{hash, sign}` (EUF-CMA).
With the checksum: exactly 127 bits when key generation or verification hashes are charged;
otherwise 124 bits when the signer's hashes and the signing requests are charged, 123 bits when
only the signer's hashes are, and 122 bits when neither is, under both notions.
-/

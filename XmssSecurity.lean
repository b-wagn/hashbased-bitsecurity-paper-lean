import XmssSecurity.Statement.StrongUnforgeabilityTheorems
import XmssSecurity.Statement.UnforgeabilityTheorems

/-!
# Security of XMSS in the random-oracle model

The public entry point for the `XmssSecurity` library. Importing this module checks the exact
classifications of strong (SUF-CMA) and standard (EUF-CMA) unforgeability under all sixteen
counting modes:

* `xmss_sufCma_exact` (`Statement/StrongUnforgeabilityTheorems.lean`): exactly 122 bits when no
  honest-party hashes are charged, and exactly 127 bits when key generation, signer, or
  verification hashes are charged.
* `xmss_eufCma_exact` (`Statement/UnforgeabilityTheorems.lean`): exactly 126 bits for direct
  queries alone, and exactly 127 bits when any additional query class is charged.
-/

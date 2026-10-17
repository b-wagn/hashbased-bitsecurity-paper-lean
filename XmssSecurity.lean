import XmssSecurity.Statement.StrongUnforgeabilityTheorems
import XmssSecurity.Statement.UnforgeabilityTheorems

/-!
# Security of XMSS in the random-oracle model

The public entry point for the `XmssSecurity` library. Importing this module checks the exact
classifications of strong (SUF-CMA) and standard (EUF-CMA) unforgeability under all sixteen
counting modes that charge the adversary's own hash queries:

* `xmss_sufCma_exact` (`Statement/StrongUnforgeabilityTheorems.lean`) and `xmss_eufCma_exact`
  (`Statement/UnforgeabilityTheorems.lean`): exactly 127 bits when key generation or verification
  hashes are charged; otherwise exactly 124 bits when the signer's hashes and the signing requests
  are charged, 123 bits when only the signer's hashes are, and 122 bits when neither is.
-/

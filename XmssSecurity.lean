import XmssSecurity.StrongUnforgeability
import XmssSecurity.Unforgeability

/-!
# Security of XMSS in the random-oracle model

The public entry point for the single `XmssSecurity` library. Importing this module
checks the security proofs and matching attacks for strong (SUF-CMA) and standard
(EUF-CMA) unforgeability under all sixteen counting modes.

* `xmss_sufCma_exact`: exactly 122 bits when no honest-party hashes are charged,
  and exactly 127 bits when key generation, signing hashes, or verification is charged.
* `xmss_eufCma_exact`: exactly 126 bits for direct queries alone, and exactly
  127 bits when any additional query class is charged.

The theorem modules retain the individual bounds and their axiom guards.
-/

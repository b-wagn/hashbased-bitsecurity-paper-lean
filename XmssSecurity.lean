import XmssSecurity.Statement.StrongUnforgeabilityTheorems
import XmssSecurity.Statement.UnforgeabilityTheorems
import XmssSecurity.Statement.CorrectnessTheorems

/-!
# Security of XMSS in the random-oracle model

Importing this module checks the SUF-CMA/EUF-CMA classifications, the two checksum bounds
with a gap below one bit, and the two correctness bounds for target-sum and checksum XMSS.
See `Statement/*Theorems.lean` for the claims and the README for the results table and build
instructions.
-/

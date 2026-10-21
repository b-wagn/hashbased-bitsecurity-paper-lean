import VCVio.OracleComp.ProbComp

/-!
# Epoch-based signature schemes

Signing and verification take an epoch `ep : Fin L`. Signing may fail (`none`).
The oracle specification `spec` supplies randomness and hashing. The generic syntax permits
randomized algorithms; XMSS signing and verification are deterministic given the hash oracle.
Correctness is defined in `Security/Correctness.lean`.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- Key generation, signing, and verification for a scheme with `L` epochs. -/
structure EpochBasedSignature {ι : Type} (spec : OracleSpec ι) (PK SK Msg Sig : Type)
    (L : ℕ) where
  /-- `Gen → (pk, sk)`. -/
  keygen : OracleComp spec (PK × SK)
  /-- `Sign(sk, ep, m) → σ ∈ Σ ∪ {⊥}`; `none` is the failure symbol `⊥`. -/
  sign : SK → Fin L → Msg → OracleComp spec (Option Sig)
  /-- `Verify(pk, ep, m, σ) → {0, 1}`. -/
  verify : PK → Fin L → Msg → Sig → OracleComp spec Bool

end XmssSecurity

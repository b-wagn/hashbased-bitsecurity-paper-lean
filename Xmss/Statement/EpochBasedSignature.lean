import VCVio.OracleComp.ProbComp

/-!
# Epoch-based signature schemes
-/

open OracleComp OracleSpec

namespace Xmss

/-- Key generation, signing, and verification for a scheme with `L` epochs. -/
structure EpochBasedSignature {ι : Type} (spec : OracleSpec ι) (PK SK Msg Sig : Type)
    (L : ℕ) where
  /-- `Gen → (pk, sk)`. -/
  keygen : OracleComp spec (PK × SK)
  /-- `Sign(sk, ep, m) → σ ∈ Σ ∪ {⊥}`; `none` is the failure symbol `⊥`. -/
  sign : SK → Fin L → Msg → OracleComp spec (Option Sig)
  /-- `Verify(pk, ep, m, σ) → {0, 1}`. -/
  verify : PK → Fin L → Msg → Sig → OracleComp spec Bool

end Xmss

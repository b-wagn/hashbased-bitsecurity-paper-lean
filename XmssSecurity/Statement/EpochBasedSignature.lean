import VCVio.OracleComp.ProbComp

/-!
# Epoch-based signature schemes

The syntax of an epoch-based signature scheme, called a synchronized signature scheme in
Definition 7 of *Hash-Based Multi-Signatures for Post-Quantum Ethereum* (Drake, Khovratovich,
Kudinov, Wagner; eprint 2025/055): a lifetime `L` and three algorithms `Gen`, `Sig`, `Ver`, where signing and verification
take an epoch `ep ∈ [L]` in addition to the message. Signing may fail, returning `⊥`.

All algorithms are oracle computations over an ambient oracle specification `spec`. In the
random-oracle model, `spec` provides private uniform sampling and the hash oracle
(`RandomOracleModel.World`). The syntax does not restrict which algorithms are randomized; for
XMSS only key generation samples, and signing and verification are deterministic given the
oracle.

Correctness (the paper's correctness error `δ`) is not part of the statements of this development.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-- An epoch-based signature scheme with lifetime `L`: public keys `PK`, secret keys `SK`,
messages `Msg`, signatures `Sig`, and epochs `Fin L`, with algorithms in `OracleComp spec`. -/
structure EpochBasedSignature {ι : Type} (spec : OracleSpec ι) (PK SK Msg Sig : Type)
    (L : ℕ) where
  /-- `Gen → (pk, sk)`. -/
  keygen : OracleComp spec (PK × SK)
  /-- `Sig(sk, ep, m) → σ ∈ Σ ∪ {⊥}`; `none` is the failure symbol `⊥`. -/
  sign : SK → Fin L → Msg → OracleComp spec (Option Sig)
  /-- `Ver(pk, ep, m, σ) → {0, 1}`. -/
  verify : PK → Fin L → Msg → Sig → OracleComp spec Bool

end XmssSecurity

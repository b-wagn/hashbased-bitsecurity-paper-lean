import Xmss.Proof.Generic.EncodingRejectionProbability
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-! The checksummed signer fails with probability below `1/128`: every digest is accepted, so
only a repeated randomizer can make it fail. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.Checksum

theorem capped_rejection_bound_lt :
    (1 - Code.acceptanceProbability) ^ Code.signingAttemptLimit +
      (Code.signingAttemptLimit : ℝ≥0∞) * Code.signingAttemptLimit *
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 128 := by
  rw [code_acceptanceProbability, code_signingAttemptLimit]
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [signingAttemptLimit, digestBits, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- In the reference scheme, a fresh signing request succeeds with probability greater than
`127/128`; randomizer repetitions are included in the failure bound. -/
theorem Signing.precomputedCappedSign_failure_lt
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : cachedEncodingInputCount cache secretKey.parameter = 0) :
    Pr[fun result : Option Generic.Signature × QueryCache HashSpec => result.1 = none |
      (simulateQ romImpl
        (Signing.precomputedCappedSign secretKey leafIndex message)).run cache] <
      1 / 128 := by
  rw [Signing.precomputedCappedSign]
  have hbound := Signing.precomputedSignBoundedAttempts_failure_le
    Code.signingAttemptLimit secretKey leafIndex message cache 0
    (by simpa using hcache.le)
  simp only [Nat.cast_zero, zero_add] at hbound
  exact hbound.trans_lt capped_rejection_bound_lt

theorem Signing.precomputedCappedSign_success_gt
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : cachedEncodingInputCount cache secretKey.parameter = 0) :
    127 / 128 < Pr[fun result : Option Generic.Signature × QueryCache HashSpec =>
      result.1 ≠ none |
      (simulateQ romImpl
        (Signing.precomputedCappedSign secretKey leafIndex message)).run cache] := by
  let computation :=
    (simulateQ romImpl
      (Signing.precomputedCappedSign secretKey leafIndex message)).run cache
  have hfailure := precomputedCappedSign_failure_lt secretKey leafIndex message cache hcache
  have hsum : Pr[fun result => result.1 = none | computation] +
      Pr[fun result => result.1 ≠ none | computation] = 1 := by
    simpa only [probFailure_of_liftM_PMF, tsub_zero] using
      probEvent_compl computation (fun result => result.1 = none)
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hsumReal
  have hfailureReal := (ENNReal.toReal_lt_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_lt_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hfailureReal ⊢
  change (Pr[fun result => result.1 = none | computation]).toReal < 1 / 128 at hfailureReal
  change 127 / 128 < (Pr[fun result => result.1 ≠ none | computation]).toReal
  linarith

/-- The reference key-generation cache meets the fresh-encoding condition. -/
theorem Signing.precomputedCappedSign_success_after_keygen
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    127 / 128 < Pr[fun result : Option Generic.Signature × QueryCache HashSpec =>
      result.1 ≠ none |
      (simulateQ romImpl
        (Signing.precomputedCappedSign keyResult.1.2 leafIndex message)).run
          keyResult.2] :=
  precomputedCappedSign_success_gt _ _ _ _
    (Keygen.keygen_cachedEncodingInputCount_eq_zero keyResult hkey)

/-- info: 'Xmss.Checksum.Signing.precomputedCappedSign_success_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Signing.precomputedCappedSign_success_after_keygen

end Xmss.Checksum

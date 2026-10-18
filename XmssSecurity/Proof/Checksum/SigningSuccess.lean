import XmssSecurity.Proof.Generic.EncodingRejectionProbability
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-! The checksummed signer fails with probability below `1/128`: every digest is accepted, so
only a repeated randomizer can make it fail. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum

theorem Checksum.capped_rejection_bound_lt :
    (1 - Generic.Code.acceptanceProbability) ^ Generic.Code.signingAttemptLimit +
      (Generic.Code.signingAttemptLimit : ℝ≥0∞) * Generic.Code.signingAttemptLimit *
        ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 128 := by
  rw [code_acceptanceProbability, code_signingAttemptLimit]
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [signingAttemptLimit, randomnessBits, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- In the reference scheme, a fresh signing request succeeds with probability greater than
`127/128`; randomizer repetitions are included in the failure bound. -/
theorem Concrete.precomputedCappedSign_failure_lt
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : Generic.cachedEncodingInputCount cache secretKey.parameter = 0) :
    Pr[fun result : Option Generic.Signature × QueryCache HashSpec => result.1 = none |
      (simulateQ Generic.romImpl
        (Generic.Concrete.precomputedCappedSign secretKey leafIndex message)).run cache] <
      1 / 128 := by
  rw [Generic.Concrete.precomputedCappedSign]
  have hbound := Generic.Concrete.precomputedSignBoundedAttempts_failure_le
    Generic.Code.signingAttemptLimit secretKey leafIndex message cache 0
    (by simpa using hcache.le)
  simp only [Nat.cast_zero, zero_add] at hbound
  exact hbound.trans_lt Checksum.capped_rejection_bound_lt

theorem Concrete.precomputedCappedSign_success_gt
    (secretKey : Generic.SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec)
    (hcache : Generic.cachedEncodingInputCount cache secretKey.parameter = 0) :
    127 / 128 < Pr[fun result : Option Generic.Signature × QueryCache HashSpec =>
      result.1 ≠ none |
      (simulateQ Generic.romImpl
        (Generic.Concrete.precomputedCappedSign secretKey leafIndex message)).run cache] := by
  let computation :=
    (simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign secretKey leafIndex message)).run cache
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
theorem Concrete.precomputedCappedSign_success_after_keygen
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    127 / 128 < Pr[fun result : Option Generic.Signature × QueryCache HashSpec =>
      result.1 ≠ none |
      (simulateQ Generic.romImpl
        (Generic.Concrete.precomputedCappedSign keyResult.1.2 leafIndex message)).run
          keyResult.2] :=
  precomputedCappedSign_success_gt _ _ _ _
    (Generic.Concrete.keygen_cachedEncodingInputCount_eq_zero keyResult hkey)

/-- info: 'XmssSecurity.Checksum.Concrete.precomputedCappedSign_success_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.precomputedCappedSign_success_after_keygen

end XmssSecurity.Checksum

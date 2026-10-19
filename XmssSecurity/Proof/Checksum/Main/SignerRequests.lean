import XmssSecurity.Proof.Checksum.Main.PaperGames

/-! Sub-bit bounds for the checksum mode that charges direct hashes, signer hashes and requests.
The proof gives 124 bits; the attack rules out work factor `3 · 2^128 / 32`.
Their ratio is `3/2 < 2`. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Proof

open SUFCMA Attack

private theorem factor_ratio :
    ((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32 < 2 * ((2 ^ 124 : ℕ) : ℝ≥0∞) := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

private theorem factor_attack_ratio :
    (3 : ℝ≥0∞) / (((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32) = 1 / ((2 ^ 123 : ℕ) : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by finiteness) (by norm_num)) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem sufCma_signerRequests_bounds :
    (SUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasTightClassicalSecurityBounds
      Generic.xmss {QueryKind.hash, QueryKind.signer, QueryKind.sign}
      ((2 ^ 124 : ℕ) : ℝ≥0∞) (((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32) := by
  refine ⟨by norm_num [ENNReal.div_pos_iff], factor_ratio, ?_, ?_⟩
  · apply SUFCMA.hasClassicalSecurityBound_of_lossy
    rw [Modes.hasClassicalSecurityBound_iff _ (by decide), modeOf_hash_signer_sign]
    exact Modes.sufCmaSignerRequests_124
  · intro h
    have hsecure := Modes.notion_oneRequest_bound_factor _ (by decide) Generic.xmss _ h
    rw [modeOf_hash_signer_sign] at hsecure
    have hbound := hsecure 3 (by norm_num) Generic.Attack.chainMutationSufCmaAdversary
      chainMutation_oneRequest (by simpa using chainMutation_signer_queryBound true)
    rw [chainMutation_signer_advantage, show (↑(3 : ℕ) : ℝ≥0∞) = 3 from rfl,
      factor_attack_ratio] at hbound
    exact (not_lt_of_ge hbound) chainMutation_seeded_advantage_exceeds_123

theorem eufCma_signerRequests_bounds :
    (EUFCMA.securityGame (PK := PublicKey) (SK := Generic.Seeded.SecretKey)).HasTightClassicalSecurityBounds
      Generic.xmss {QueryKind.hash, QueryKind.signer, QueryKind.sign}
      ((2 ^ 124 : ℕ) : ℝ≥0∞) (((3 * 2 ^ 128 : ℕ) : ℝ≥0∞) / 32) := by
  refine ⟨by norm_num [ENNReal.div_pos_iff], factor_ratio, ?_, ?_⟩
  · apply SUFCMA.hasClassicalSecurityBound_of_lossy
    rw [Modes.eufHasClassicalSecurityBound_iff _ (by decide), modeOf_hash_signer_sign]
    intro q hq adversary hbound
    exact (EUFCMA.advantage_le_strong _ Generic.xmss adversary).trans
      (Modes.sufCmaSignerRequests_124 q hq adversary
        ((EUFCMA.hasQueryBound_iff_strong _ Generic.xmss adversary q).1 hbound))
  · intro h
    have hsecure := Modes.eufNotion_oneRequest_bound_factor _ (by decide) Generic.xmss _ h
    rw [modeOf_hash_signer_sign] at hsecure
    have hbound := hsecure 3 (by norm_num) freshSufCmaAdversary fresh_oneRequest
      (by simpa using freshMessage_queryBound true true)
    rw [show (↑(3 : ℕ) : ℝ≥0∞) = 3 from rfl, factor_attack_ratio] at hbound
    exact (not_lt_of_ge ((freshMessage_standard_advantage_lower _).trans hbound))
      fresh_seeded_advantage_exceeds_123

end XmssSecurity.Checksum.Proof

import Xmss.Proof.Generic.Scheme.Xmss
import Xmss.Statement.UnforgeabilityGame
import Xmss.Proof.Common.EUFCMA.Modes
import Xmss.Proof.Generic.Modes.Exact
import Xmss.Proof.Common.Legacy.PerModeNotionsEUFCMA
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Five minimal security modes and two attacks characterize all sixteen
standard-unforgeability modes: direct-only has 126 bits, all others have 127. -/

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Unforgeability hiding experiment

theorem secure_127_of_minimal_modes
    (hk : (EUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hs : (EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hv : (EUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hr : (EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss 127)
    (mode : CountingMode) (h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true) :
    (EUFCMA.notion mode).HasClassicalSecurityBits Generic.xmss 127 := by
  simp only [Bool.or_eq_true] at h
  rcases h with ((hkeygen | hsigner) | hverifier) | hrequests
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hkeygen]) Generic.xmss 127 hk
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hsigner]) Generic.xmss 127 hs
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hverifier]) Generic.xmss 127 hv
  · exact hasClassicalSecurityBits_of_le (by simp [CountingMode.Le, hrequests]) Generic.xmss 127 hr

theorem exactStatement_of_basis
    (hd : (EUFCMA.notion Unforgeability.CountingMode.direct).HasClassicalSecurityBits Generic.xmss 126)
    (hk : (EUFCMA.notion ⟨true, false, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hs : (EUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hv : (EUFCMA.notion ⟨false, false, true, false⟩).HasClassicalSecurityBits Generic.xmss 127)
    (hr : (EUFCMA.notion ⟨false, false, false, true⟩).HasClassicalSecurityBits Generic.xmss 127)
    (ha126 : ¬(EUFCMA.notion Unforgeability.CountingMode.direct).HasClassicalSecurityBits Generic.xmss (126 + 1))
    (ha127 : ¬(EUFCMA.notion Unforgeability.CountingMode.everything).HasClassicalSecurityBits Generic.xmss (127 + 1)) : (∀ mode : Unforgeability.CountingMode, (EUFCMA.notion mode).HasExactClassicalSecurityBits Generic.xmss (if mode.keygen || mode.signer || mode.verifier || mode.requests then 127 else 126)) := by
  intro mode
  by_cases h : (mode.keygen || mode.signer || mode.verifier || mode.requests) = true
  · rw [if_pos h]
    exact ⟨secure_127_of_minimal_modes hk hs hv hr mode h,
      not_hasClassicalSecurityBits_of_le (Modes.le_everything mode) Generic.xmss 128 ha127⟩
  · rw [if_neg h]
    have hnone : mode.keygen = false ∧ mode.signer = false ∧ mode.verifier = false ∧ mode.requests = false := by
      simpa only [Bool.or_eq_true, not_or, Bool.not_eq_true, and_assoc] using h
    have hmode : mode = CountingMode.direct := by
      cases mode
      simp_all [CountingMode.direct]
    subst mode
    exact ⟨hd, ha126⟩

end Xmss.TargetSum.EUFCMA

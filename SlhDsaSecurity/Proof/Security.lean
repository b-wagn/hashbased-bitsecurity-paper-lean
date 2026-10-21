import SlhDsaSecurity.Statement.Security

/-! The two notions use the same transcript, verification, and query budgets. -/

open OracleComp OracleSpec

namespace SlhDsaSecurity.Security

theorem fresh_standard_implies_strong (signed : SigningLog) (forgery : Forgery)
    (h : Fresh .standard signed forgery) : Fresh .strong signed forgery := by
  rintro ⟨entry, hentry, hmessage, _⟩
  exact h ⟨entry, hentry, hmessage⟩

theorem advantage_standard_le_strong (adversary : Adversary) :
    advantage .standard adversary ≤ advantage .strong adversary := by
  apply probEvent_mono''
  intro outcome h
  exact ⟨h.1, fresh_standard_implies_strong outcome.signed outcome.forgery h.2⟩

/-- An eventual SUF-CMA bound yields EUF-CMA at the same work factor and lifetime. -/
theorem strong_implies_standard (bits : Nat) (h : HasSecurityBits .strong bits) :
    HasSecurityBits .standard bits := by
  intro q hq adversary hbudget
  exact (advantage_standard_le_strong adversary).trans (h q hq adversary hbudget)

end SlhDsaSecurity.Security

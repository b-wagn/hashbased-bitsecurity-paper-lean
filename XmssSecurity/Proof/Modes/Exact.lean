import XmssSecurity.Statement.Scheme.Xmss
import XmssSecurity.Proof.Modes.Lattice
import XmssSecurity.Proof.Legacy.PerModeNotionsEUFCMA

/-!
# The extreme counting modes

Every counting mode lies between `direct`, which charges only the adversary's own hash queries,
and `everything`; security in `direct` and attacks in `everything` transfer to every mode
(`Classification.lean`).
-/

namespace XmssSecurity.Modes

open SUFCMA

theorem direct_le (mode : CountingMode) : CountingMode.direct.Le mode := by
  simp [CountingMode.Le, CountingMode.direct]

theorem le_everything (mode : CountingMode) : mode.Le CountingMode.everything := by
  simp [CountingMode.Le, CountingMode.everything]

end XmssSecurity.Modes

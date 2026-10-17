import XmssSecurity.Proof.Checksum.Scheme.Xmss
import XmssSecurity.Proof.Common.Modes.Lattice
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-!
# The extreme counting modes

Every counting mode lies between `direct`, which charges only the adversary's own hash queries,
and `everything`; security in `direct` and attacks in `everything` transfer to every mode
(`Classification.lean`).
-/

namespace XmssSecurity.Checksum.Modes
open XmssSecurity.Modes

open SUFCMA

theorem direct_le (mode : CountingMode) : CountingMode.direct.Le mode := by
  simp [CountingMode.Le, CountingMode.direct]

theorem le_everything (mode : CountingMode) : mode.Le CountingMode.everything := by
  simp [CountingMode.Le, CountingMode.everything]

end XmssSecurity.Checksum.Modes

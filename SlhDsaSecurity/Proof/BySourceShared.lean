import SlhDsaSecurity.Proof.ShareFinal
import SlhDsaSecurity.Proof.BySourceBridge

/-!
# The shared half, with the signer's calls free

`ShareFinal.hshared` reads the budget in two places, and neither needs the signer's calls. The
cap `L = q - (chains + 1) · 2 ^ subtreeHeight` is a cap on the adversary's own calls plus one per
served request, and `ShareRealCap.cost_le_of_budget` pays for it out of the total count by
noting that key generation spends its top tree and each served request costs the signer two
calls. With the requests counted directly, the second half of that is not needed: a served
request is a request, and requests are in the budget. So `cost_le_of_tail` reads the same cap
off `BySourceBridge.TailBudget`, and the rest of the half is `ShareFinal`'s, line for line.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceShared

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent ShareRealCap BySourceBridge

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

theorem servedCount_le_length (log : SigningLog) :
    AdversaryQueries.servedCount log ≤ log.length :=
  List.length_filter_le _ _

end SlhDsaSecurity.BySourceShared

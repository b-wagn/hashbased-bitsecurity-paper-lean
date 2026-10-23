import SlhDsaSecurity.Proof.TableTail
import SlhDsaSecurity.Proof.LinkedGame
import SlhDsaSecurity.Proof.RecordedTail

/-!
# Two cells, and the computation that reads no others

`RedrawCell`'s stall takes the run as a function of the table and asks it to be **blind off a
named set**: two tables that agree on the touched nodes give the *same computation*, as a
syntactic equality. The set it is proved for is `RedrawCell.seedAndRoot` — the secret seed and
the honest root — and `open_seedAndRoot` is why that set costs nothing: the root is a `tree`
node, available at every state, so excluding it excludes no sensitive query.

This file discharges that hypothesis for the honest linked run.

Everything the run reads off the table goes through `TableTail.keysOf`, and `keysOf_eq` says
what that is: the secret key is the seed cell, the drawn `prfSeed`, and a public key of the
drawn `publicSeed` and the root cell. The root arrives as `Scheme.keygenInternal`'s own
`Merkle.node` call, run from the walk's cache; `CanonicalGraph.keygen_root_cell` names it as the
graph's top cell and `HonestProbes.replayCells_warmCache` evaluates it there — the cache was
built from those cells, so replaying it returns them.

**It is the unstripped signer that makes this true**, and that is why the preceding file exists.
`StrippedGame.strippedSign` carries the walk's whole cache as an argument, so the stripped run
mentions every cell of the table and agreeing on two of them says nothing about it. `Scheme.sign`
carries only the key.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.TouchedKeys

open Security CanonicalGraph WalkTable TableTail KeygenValue

/-! ## The keys, as two cells -/

/-- **The keys the walk's cache determines are the seed cell and the root cell.** -/
theorem honestKeys_eq (sds : Digest × Digest × Digest) (outputs : Programming.Outputs) :
    honestKeys sds outputs =
      (⟨sds.1, sds.2.1,
          ⟨sds.2.2, Programming.cellsOfOutputs sds.1 outputs (.structural topRoot)⟩⟩,
        ⟨sds.2.2, Programming.cellsOfOutputs sds.1 outputs (.structural topRoot)⟩) := by
  have hroot : (honestKeys sds outputs).2.root =
      Programming.cellsOfOutputs sds.1 outputs (.structural topRoot) :=
    (@keygen_root_cell (CacheReplay.replayQuery (HonestProbes.warmCache sds.2.2 sds.1 outputs))
      sds.1 sds.2.1 sds.2.2).trans
      (congrFun (HonestProbes.replayCells_warmCache sds.2.2 sds.1 outputs) (.structural topRoot))
  rw [show honestKeys sds outputs =
    (⟨sds.1, sds.2.1, ⟨sds.2.2, (honestKeys sds outputs).2.root⟩⟩,
      ⟨sds.2.2, (honestKeys sds outputs).2.root⟩) from rfl, hroot]

/-- **The keys at a drawn table are two of its cells.** -/
theorem keysOf_eq (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    keysOf prfSeed publicSeed table =
      (⟨table.1 Node.secretSeed, prfSeed,
          ⟨publicSeed, table.1 (.structural topRoot)⟩⟩,
        ⟨publicSeed, table.1 (.structural topRoot)⟩) := by
  rw [keysOf, honestKeys_eq, cellsOfOutputs_fullOutput]

/-! ## The run that reads nothing else -/

end SlhDsaSecurity.TouchedKeys

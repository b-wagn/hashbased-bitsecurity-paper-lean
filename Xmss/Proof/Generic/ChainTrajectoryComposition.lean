import Xmss.Proof.Generic.ChainTrajectoryUniformity

namespace Xmss.Generic

variable [Code]

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

noncomputable def allLeafIndices : List LeafIndex :=
  Finset.univ.toList

omit [Code] in
theorem allLeafIndices_nodup : allLeafIndices.Nodup := by
  exact Finset.nodup_toList Finset.univ

omit [Code] in
theorem mem_allLeafIndices (leafIndex : LeafIndex) : leafIndex ∈ allLeafIndices := by
  simp [allLeafIndices]

omit [Code] in
theorem allLeafIndices_length : allLeafIndices.length = lifetime := by
  simp [allLeafIndices, LeafIndex]

attribute [irreducible] allLeafIndices

end Xmss.Generic

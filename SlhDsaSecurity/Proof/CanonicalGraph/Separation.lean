import SlhDsaSecurity.Proof.CanonicalGraph.Input
import SlhDsaSecurity.Proof.HashSeparation

/-! Every canonical structural coordinate fits the existing shared-input separation bound. -/

namespace SlhDsaSecurity.CanonicalGraph

private theorem zero32 : BitVec.toNat (0 : BitVec 32) = 0 := rfl

end SlhDsaSecurity.CanonicalGraph

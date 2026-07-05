module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S198

/- Space 198: Disjoint union of the reals and a singleton.
See https://topology.pi-base.org/spaces/S000198.
The disjoint union X = ℝ ⊔ {⋆} of ℝ (S25) and the singleton space (S162), topologized
via the standard coproduct topology on `ℝ ⊕ Unit` (coinduced by the two inclusions). -/

/-- Disjoint union of the reals and a singleton (pi-Base S198). -/
def S198 : Type := ℝ ⊕ Unit

instance : TopologicalSpace S198 := inferInstanceAs (TopologicalSpace (ℝ ⊕ Unit))

end S198
end PiBase.Spaces

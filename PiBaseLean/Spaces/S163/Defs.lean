module

public import Mathlib.Topology.Order

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S163

/- Space 163: The Empty Space.
See https://topology.pi-base.org/spaces/S000163.
X = ∅ with its only valid topology {∅}. -/

/-- The Empty Space (pi-Base S163). -/
def S163 : Type := Empty

instance : TopologicalSpace S163 := TopologicalSpace.generateFrom {∅}

instance : IsEmpty S163 := inferInstanceAs (IsEmpty Empty)

end S163
end PiBase.Spaces

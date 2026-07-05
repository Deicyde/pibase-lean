module

public import Mathlib.Order.Monotone.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UnitInterval

@[expose] public section

open Topology

namespace PiBase.Spaces
namespace S105

/- Space 105: Helly space.
See https://topology.pi-base.org/spaces/S000105.
The subspace of `unitInterval → unitInterval` (π-Base S103, with the product topology)
consisting of all non-decreasing functions `unitInterval → unitInterval`. -/

/-- Helly space: the non-decreasing functions `unitInterval → unitInterval`
(pi-Base S105). -/
def S105 : Type := {f : unitInterval → unitInterval // Monotone f}

instance : TopologicalSpace S105 := instTopologicalSpaceSubtype

end S105
end PiBase.Spaces

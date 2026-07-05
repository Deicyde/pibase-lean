module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Order.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S33

/- Space 33: Ordinal space ω+ω.
See https://topology.pi-base.org/spaces/S000033.
The set of ordinals below the second limit ordinal ω+ω, with the order topology. -/

/-- Ordinal space ω+ω (pi-Base S33): the ordinals below the second limit ordinal `ω+ω`,
carrying the order topology. -/
def S33 : Type 1 := {o : Ordinal.{0} // o < ω + ω}

noncomputable instance : LinearOrder S33 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω + ω})

noncomputable instance : TopologicalSpace S33 := Preorder.topology S33

instance : OrderTopology S33 := ⟨rfl⟩

end S33
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S33 as a bundled `Space` (carrier + topology). -/
noncomputable def S33 : Space := ⟨PiBase.Spaces.S33.S33, inferInstance⟩

end PiBase.Formal

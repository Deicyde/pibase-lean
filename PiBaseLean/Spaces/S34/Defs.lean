module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Order.Basic

public import PiBaseLean.Spaces.Bundled.Defs

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S34

/- Space 34: Ordinal space ω+ω+1.
See https://topology.pi-base.org/spaces/S000034.
The set of ordinals at most the second limit ordinal ω+ω, with the order topology. -/

/-- Ordinal space ω+ω+1 (pi-Base S34): the ordinals at most the second limit ordinal `ω+ω`,
carrying the order topology. -/
def S34 : Type 1 := {o : Ordinal.{0} // o ≤ ω + ω}

noncomputable instance : LinearOrder S34 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o ≤ ω + ω})

noncomputable instance S34_top : TopologicalSpace S34 := Preorder.topology S34

instance : OrderTopology S34 := ⟨rfl⟩

end S34
end PiBase.Spaces

namespace PiBase.Formal

/-- π-Base S34 as a bundled `Space` (carrier + topology). -/
noncomputable def S34 : Space := ⟨PiBase.Spaces.S34.S34, PiBase.Spaces.S34.S34_top⟩

end PiBase.Formal

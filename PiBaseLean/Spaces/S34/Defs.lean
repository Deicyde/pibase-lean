module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Order.Basic

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

noncomputable instance : TopologicalSpace S34 := Preorder.topology S34

instance : OrderTopology S34 := ⟨rfl⟩

end S34
end PiBase.Spaces

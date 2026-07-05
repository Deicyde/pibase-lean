module

public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.Topology.Order.Basic

@[expose] public section

open Topology Ordinal

namespace PiBase.Spaces
namespace S35

/- Space 35: Ordinal space ω₁.
See https://topology.pi-base.org/spaces/S000035.
The set of ordinals below the least uncountable ordinal ω₁, with the order topology. -/

/-- Ordinal space ω₁ (pi-Base S35): the ordinals below the least uncountable ordinal,
carrying the order topology. -/
def S35 : Type 1 := {o : Ordinal.{0} // o < ω₁}

noncomputable instance : LinearOrder S35 :=
  inferInstanceAs (LinearOrder {o : Ordinal.{0} // o < ω₁})

noncomputable instance : TopologicalSpace S35 := Preorder.topology S35

instance : OrderTopology S35 := ⟨rfl⟩

end S35
end PiBase.Spaces
